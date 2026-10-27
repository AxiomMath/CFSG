module

public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofStatements
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.RankThree.PartOne.S11.SecTenEight

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res7Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Subgroup

section Layer

variable {P Q : Type*} [Group P] [Group Q]

theorem not_le_of_isQuasisimple {K Z : Subgroup P} (hK : IsQuasisimple K) (hZ : Z ≤ center P) :
    ¬ K ≤ Z := by
  intro hKZ
  obtain ⟨-, -, a, b, hab⟩ := hK
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (center K) a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (center K) b
  apply hab
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have h := mem_center_iff.mp (hZ (hKZ a'.2)) (b' : P)
  simp only [coe_mul]
  exact h.symm

theorem isComponent_map_of_surjective (f : P →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ center P) {K : Subgroup P} (hK : IsComponent K) :
    IsComponent (K.map f) :=
  ⟨LocalCores.isQuasisimple_map hK.1 f (not_le_of_isQuasisimple hK.1 hker), hK.2.map hf⟩

theorem exists_isComponent_map_eq (f : P →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ center P) {R : Subgroup Q} (hR : IsComponent R) :
    ∃ K : Subgroup P, IsComponent K ∧ K.map f = R := by
  set H := R.comap f with hH
  set fH : H →* R := (f.comp H.subtype).codRestrict R (fun h => h.2) with hfH
  have hfHs : Function.Surjective fH := by
    rintro ⟨r, hr⟩
    obtain ⟨p, rfl⟩ := hf r
    exact ⟨⟨p, hr⟩, rfl⟩
  have hfHker : fH.ker ≤ center H := by
    intro h hh
    have h1 : (h : P) ∈ f.ker := by
      rw [MonoidHom.mem_ker] at hh ⊢
      exact congrArg Subtype.val hh
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hker h1) y)
  have hq := LocalCores.quasisimple_central_extension_derived_of_surjective fH hfHs hfHker hR.1
  obtain ⟨-, -, hsurj⟩ :=
    LocalCores.central_extension_derived_of_surjective fH hfHs hfHker hR.1.1
  refine ⟨(commutator H).map H.subtype, ⟨?_, ?_⟩, ?_⟩
  · exact LocalCores.isQuasisimple_of_mulEquiv
      ((commutator H).equivMapOfInjective H.subtype H.subtype_injective) hq
  · have hHs : H.IsSubnormal := hR.2.comap f
    exact (Subgroup.Normal.isSubnormal (commutator_normal ⊤ ⊤)).trans' hHs
  · apply le_antisymm
    · rintro _ ⟨_, ⟨h, -, rfl⟩, rfl⟩
      exact h.2
    · intro r hr
      obtain ⟨⟨h, hh⟩, hhr⟩ := hsurj ⟨r, hr⟩
      refine ⟨h, ⟨h, hh, rfl⟩, ?_⟩
      exact congrArg Subtype.val hhr

theorem map_layer_of_surjective (f : P →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ center P) : (layer P).map f = layer Q := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← map_le_iff_le_comap]
    exact LocalCores.component_le_layer (isComponent_map_of_surjective f hf hker hK)
  · refine sSup_le fun R hR => ?_
    obtain ⟨K, hK, rfl⟩ := exists_isComponent_map_eq f hf hker hR
    exact map_mono (LocalCores.component_le_layer hK)

end Layer

section Theta

variable {P Q : Type*} [Group P] [Group Q] [Finite P] [Finite Q]

theorem theta_eq_ker (f : P →* Q) (hf : Function.Surjective f) (hker : f.ker ≤ center P)
    (hker3 : ¬ 3 ∣ Nat.card f.ker) (hQ : aschbacherSolvableCore 3 Q = ⊥) :
    aschbacherSolvableCore 3 P = f.ker := by
  obtain ⟨hTs, hTch, hT3, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := P) Nat.prime_three
  obtain ⟨-, -, -, hmaxQ, -⟩ :=
    solvable_prime_complement_core_characterization (H := Q) Nat.prime_three
  apply le_antisymm
  · have hTn : (aschbacherSolvableCore 3 P).Normal := normal_of_characteristic _
    have himg : (aschbacherSolvableCore 3 P).map f ≤ aschbacherSolvableCore 3 Q := by
      refine hmaxQ _ (hTn.map f hf) ?_ ?_
      · exact Group.isSolvable_of_surjective (f := f.subgroupMap _) (f.subgroupMap_surjective _)
      · intro h3
        exact hT3 (h3.trans (card_map_dvd _ _))
    rw [hQ, le_bot_iff, Subgroup.map_eq_bot_iff] at himg
    exact himg
  · refine hmax _ f.normal_ker ?_ hker3
    refine Group.isSolvable_of_comm fun a b => ?_
    exact Subtype.ext (mem_center_iff.mp (hker b.2) a)

theorem theta_eq_bot_of_center (hQ : IsQuasisimple Q) (hZ : ∀ z ∈ center Q, z ^ 3 = 1) :
    aschbacherSolvableCore 3 Q = ⊥ := by
  have hθZ := PartOne.theta_le_center_of_quasisimple Nat.prime_three hQ
  obtain ⟨-, -, hT3, -⟩ := solvable_prime_complement_core_characterization (H := Q)
    Nat.prime_three
  rw [eq_bot_iff]
  intro t ht
  rw [mem_bot]
  have h1 : orderOf t ∣ 3 := orderOf_dvd_of_pow_eq_one (hZ t (hθZ ht))
  have h2 : orderOf (⟨t, ht⟩ : aschbacherSolvableCore 3 Q) ∣
      Nat.card (aschbacherSolvableCore 3 Q) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h2
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h2
    exact absurd h2 hT3

end Theta

theorem mem_of_eq_mul_central {P : Type*} [Group P] {H : Subgroup P} {d i k : P}
    (hd3 : d ^ 3 = 1) (hk : ∀ g : P, g * k = k * g) (hk3 : ¬ 3 ∣ orderOf k) (hi : i ∈ H)
    (hdik : d = i * k) : d ∈ H := by
  set m := orderOf k with hm
  have hcomm : Commute i k := (hk i)
  have hdm : d ^ m = i ^ m := by
    rw [hdik, hcomm.mul_pow, hm, pow_orderOf_eq_one, mul_one]
  have hdmH : d ^ m ∈ H := hdm ▸ pow_mem hi m
  have hcop : Nat.Coprime m 3 := (Nat.coprime_comm.mp
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hk3))
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (m * a) % 3 = 1 := by
    have h1 : m % 3 = 1 ∨ m % 3 = 2 := by
      have := Nat.mod_lt m (show 0 < 3 by norm_num)
      have h0 : m % 3 ≠ 0 := fun h0 => hk3 (Nat.dvd_of_mod_eq_zero h0)
      omega
    rcases h1 with h1 | h1
    · exact ⟨1, by rw [mul_one, h1]⟩
    · exact ⟨2, by rw [Nat.mul_mod, h1]⟩
  have hd : d = (d ^ m) ^ a := by
    rw [← pow_mul, ← Nat.mod_add_div (m * a) 3, ha, pow_add, pow_mul, hd3, one_pow, mul_one,
      pow_one]
  rw [hd]
  exact pow_mem hdmH a

section Transport

variable {G : Type} [Group G] [Finite G]

theorem range_eq_centralizer {L : Subgroup G}
    (hθZ : aschbacherSolvableCore 3 ↥L ≤ center ↥L) {d : G} (hdL : d ∈ L) (hd3 : d ^ 3 = 1) :
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)).comp
        (inclusion (inf_le_left : L ⊓ centralizer ({d} : Set G) ≤ L))).range =
      centralizer {((⟨d, hdL⟩ : L) : lBar L)} := by
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  obtain ⟨-, -, hθ3, -⟩ := solvable_prime_complement_core_characterization (H := ↥L)
    Nat.prime_three
  set d₀ : L := ⟨d, hdL⟩ with hd₀
  apply le_antisymm
  · rintro _ ⟨k, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp k.2).2
    simp only [coe_mul, coe_inclusion]
    exact h1
  · intro q hq
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θ q
    rw [mem_centralizer_singleton_iff, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq] at hq
    set t := (l * d₀)⁻¹ * (d₀ * l) with ht
    have htZ : t ∈ center ↥L := hθZ hq
    have hdt : l⁻¹ * d₀ * l = d₀ * t := by
      rw [ht]
      group
    have hd₀3 : d₀ ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    have ht3 : t ^ 3 = 1 := by
      have h1 : (l⁻¹ * d₀ * l) ^ 3 = 1 := by
        rw [show l⁻¹ * d₀ * l = l⁻¹ * d₀ * l⁻¹⁻¹ by group, conj_pow, hd₀3]
        group
      rw [hdt, (show Commute d₀ t from mem_center_iff.mp htZ d₀).mul_pow, hd₀3, one_mul] at h1
      exact h1
    have ht1 : t = 1 := by
      have h1 : orderOf t ∣ 3 := orderOf_dvd_of_pow_eq_one ht3
      have h2 : orderOf (⟨t, hq⟩ : θ) ∣ Nat.card θ := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h2
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact orderOf_eq_one_iff.mp h
      · rw [h] at h2
        exact absurd h2 hθ3
    have hld : (l : G) * d = d * l := by
      have h1 : l⁻¹ * d₀ * l = d₀ := by rw [hdt, ht1, mul_one]
      have h2 : d₀ * l = l * d₀ := by
        calc d₀ * l = l * (l⁻¹ * d₀ * l) := by group
          _ = l * d₀ := by rw [h1]
      exact (congrArg Subtype.val h2).symm
    refine ⟨⟨l, ⟨l.2, mem_centralizer_singleton_iff.mpr hld⟩⟩, ?_⟩
    rfl

theorem iOf218_transport {L : Subgroup G} (hL : IsQuasisimple ↥L) {d : G} (hdL : d ∈ L)
    (hd3 : d ^ 3 = 1) :
    (((⟨d, hdL⟩ : L) : lBar L) ∈
        inSubgroup CFSG.layer (centralizer {((⟨d, hdL⟩ : L) : lBar L)}) → d ∈ iOf218 L d) ∧
      (aschbacherSolvableCore 3
          ↥(inSubgroup CFSG.layer (centralizer {((⟨d, hdL⟩ : L) : lBar L)})) = ⊥ →
        Nonempty (lBar (iOf218 L d) ≃*
          ↥(inSubgroup CFSG.layer (centralizer {((⟨d, hdL⟩ : L) : lBar L)})))) ∧
      (aschbacherSolvableCore 3 ↥L = ⊥ →
        Nonempty (↥(iOf218 L d) ≃*
          ↥(inSubgroup CFSG.layer (centralizer {((⟨d, hdL⟩ : L) : lBar L)})))) := by
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  have hθZ : θ ≤ center ↥L := PartOne.theta_le_center_of_quasisimple Nat.prime_three hL
  obtain ⟨-, -, hθ3, -⟩ := solvable_prime_complement_core_characterization (H := ↥L)
    Nat.prime_three
  set x : lBar L := ((⟨d, hdL⟩ : L) : lBar L) with hx
  set K := L ⊓ centralizer ({d} : Set G) with hK
  set Kb := centralizer ({x} : Set (lBar L)) with hKb
  set ψ₀ : ↥K →* lBar L := (QuotientGroup.mk' θ).comp (inclusion (inf_le_left : K ≤ L))
    with hψ₀
  have hrange : ψ₀.range = Kb := range_eq_centralizer hθZ hdL hd3
  have hmemKb : ∀ k : ↥K, ψ₀ k ∈ Kb := fun k => hrange ▸ ⟨k, rfl⟩
  set ψ : ↥K →* ↥Kb := ψ₀.codRestrict Kb hmemKb with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    rw [← hrange] at hq
    obtain ⟨k, hk⟩ := hq
    exact ⟨k, Subtype.ext hk⟩
  have hψker : ∀ k : ↥K, k ∈ ψ.ker ↔ inclusion (inf_le_left : K ≤ L) k ∈ θ := by
    intro k
    rw [MonoidHom.mem_ker, ← QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hkerZ : ψ.ker ≤ center ↥K := by
    intro k hk
    rw [mem_center_iff]
    intro k'
    have h1 := mem_center_iff.mp (hθZ ((hψker k).mp hk)) (inclusion inf_le_left k')
    apply Subtype.ext
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hord : ∀ k ∈ ψ.ker, ¬ 3 ∣ orderOf k := by
    intro k hk h3
    have h1 : orderOf (⟨_, (hψker k).mp hk⟩ : θ) ∣ Nat.card θ := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, orderOf_injective _ (inclusion_injective inf_le_left)] at h1
    exact hθ3 (h3.trans h1)
  have hker3 : ∀ N : Subgroup ↥K, N ≤ ψ.ker → ¬ 3 ∣ Nat.card N := by
    intro N hN h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have h1 := hord (k : ↥K) (hN k.2)
    rw [Subgroup.orderOf_coe, hk] at h1
    exact h1 (dvd_refl 3)
  have hlayer := map_layer_of_surjective ψ hψs hkerZ
  have hmemE : ∀ i : ↥(CFSG.layer ↥K), ψ i ∈ CFSG.layer ↥Kb := fun i =>
    hlayer ▸ ⟨i, i.2, rfl⟩
  set ρ : ↥(CFSG.layer ↥K) →* ↥(CFSG.layer ↥Kb) :=
    (ψ.comp (CFSG.layer ↥K).subtype).codRestrict _ hmemE with hρ
  have hρs : Function.Surjective ρ := by
    rintro ⟨q, hq⟩
    rw [← hlayer] at hq
    obtain ⟨k, hk, hkq⟩ := hq
    exact ⟨⟨k, hk⟩, Subtype.ext hkq⟩
  have hρker : ∀ i, i ∈ ρ.ker ↔ (i : ↥K) ∈ ψ.ker := by
    intro i
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hρZ : ρ.ker ≤ center ↥(CFSG.layer ↥K) := by
    intro i hi
    rw [mem_center_iff]
    intro j
    apply Subtype.ext
    exact mem_center_iff.mp (hkerZ ((hρker i).mp hi)) j
  have hρ3 : ¬ 3 ∣ Nat.card ρ.ker := by
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨i, hi⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have h1 := hord ((i : ↥(CFSG.layer ↥K)) : ↥K) ((hρker _).mp i.2)
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hi] at h1
    exact h1 (dvd_refl 3)
  set eI : ↥(iOf218 L d) ≃* ↥(CFSG.layer ↥K) :=
    ((CFSG.layer ↥K).equivMapOfInjective K.subtype K.subtype_injective).symm with heI
  set eQ : ↥(CFSG.layer ↥Kb) ≃* ↥(inSubgroup CFSG.layer Kb) :=
    (CFSG.layer ↥Kb).equivMapOfInjective Kb.subtype Kb.subtype_injective with heQ
  refine ⟨fun hxE => ?_, fun hθE => ?_, fun hθL => ?_⟩
  ·
    obtain ⟨q, hq, hqx⟩ := hxE
    rw [← hlayer] at hq
    obtain ⟨k, hk, hkq⟩ := hq
    set d₁ : ↥K := ⟨d, ⟨hdL, mem_centralizer_singleton_iff.mpr rfl⟩⟩ with hd₁
    have hψd : ψ d₁ = q := Subtype.ext hqx.symm
    have hker : k⁻¹ * d₁ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkq, hψd, inv_mul_cancel]
    have hd₁3 : d₁ ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    have hmem := mem_of_eq_mul_central hd₁3 (fun g => (mem_center_iff.mp (hkerZ hker) g))
      (hord _ hker) hk (by group)
    exact ⟨d₁, hmem, rfl⟩
  ·
    have hθE' : aschbacherSolvableCore 3 ↥(CFSG.layer ↥Kb) = ⊥ := by
      have h1 := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eQ
      rw [hθE] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ eQ.injective).mp h1
    have hθker := theta_eq_ker ρ hρs hρZ hρ3 hθE'
    set e1 : ↥(CFSG.layer ↥K) ⧸ aschbacherSolvableCore 3 ↥(CFSG.layer ↥K) ≃*
        ↥(CFSG.layer ↥Kb) :=
      (QuotientGroup.quotientMulEquivOfEq hθker).trans
        (QuotientGroup.quotientKerEquivOfSurjective ρ hρs) with he1
    set e2 : lBar (iOf218 L d) ≃*
        ↥(CFSG.layer ↥K) ⧸ aschbacherSolvableCore 3 ↥(CFSG.layer ↥K) :=
      QuotientGroup.congr _ _ eI
        (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eI) with he2
    exact ⟨(e2.trans e1).trans eQ⟩
  ·
    have hρinj : Function.Injective ρ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro i hi
      have h1 := (hψker _).mp ((hρker i).mp hi)
      rw [hθ, hθL, mem_bot] at h1
      rw [mem_bot]
      apply Subtype.ext
      apply Subtype.ext
      have h2 := congrArg Subtype.val h1
      simpa using h2
    exact ⟨(eI.trans (MulEquiv.ofBijective ρ ⟨hρinj, hρs⟩)).trans eQ⟩

theorem isCentral_lBar {L : Subgroup G} {d : G} (hdL : d ∈ L) (hcen : IsCentral218 L d) :
    IsCentral218 (⊤ : Subgroup (lBar L)) ((⟨d, hdL⟩ : L) : lBar L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, ⟨S₀, rfl⟩, hdS⟩ := hcen
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set S₁ : Sylow 3 (lBar L) := S₀.mapSurjective hπs with hS₁
  have hS₁c : ((S₁ : Subgroup (lBar L))) = (S₀ : Subgroup ↥L).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨z, hz, hzd⟩ := hdS
  have hzd' : (z : G) = d := hzd
  have hd₀S : (⟨d, hdL⟩ : L) ∈ (S₀ : Subgroup ↥L) := by
    obtain ⟨s, hs, hsz⟩ := (z : _).2
    have hsd : (s : G) = d := by rw [← hzd']; exact hsz
    have : s = ⟨d, hdL⟩ := Subtype.ext hsd
    rw [← this]
    exact hs
  have hd₀c : ∀ s ∈ (S₀ : Subgroup ↥L), s * ⟨d, hdL⟩ = ⟨d, hdL⟩ * s := by
    intro s hs
    have h1 := mem_center_iff.mp hz ⟨s, ⟨s, hs, rfl⟩⟩
    apply Subtype.ext
    have h2 := congrArg Subtype.val h1
    simp only [coe_mul] at h2
    rw [hzd'] at h2
    exact h2
  refine ⟨(S₁ : Subgroup (lBar L)), ?_, ?_⟩
  · rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, S₁.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S₁.not_dvd_index
  · have hxS : ((⟨d, hdL⟩ : L) : lBar L) ∈ (S₁ : Subgroup (lBar L)) := by
      rw [hS₁c]
      exact ⟨_, hd₀S, rfl⟩
    refine ⟨⟨_, hxS⟩, mem_center_iff.mpr fun y => ?_, rfl⟩
    obtain ⟨s, hs, hsy⟩ := (show (y : lBar L) ∈ (S₀ : Subgroup ↥L).map π from hS₁c ▸ y.2)
    apply Subtype.ext
    simp only [coe_mul]
    rw [← hsy, show ((⟨d, hdL⟩ : L) : lBar L) = π ⟨d, hdL⟩ from rfl, ← map_mul, ← map_mul,
      hd₀c s hs]

end Transport

end CFSG.RankThree.PartTwo.Sec21.Item21Res7Proof
