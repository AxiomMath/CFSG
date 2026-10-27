module

public import CFSG.LocalAnalysis.SectionRank.QTK.ExcRee
public import CFSG.Quasithin.Background.F6NQStructure

public section

namespace CFSG.Quasithin.RonanF617

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F6
open CFSG.Quasithin.F6.F617Setting (exists_ne_one_commute exists_inv_mod_pCoreOf)

structure Setting {D : Type} [Group D] [Finite D] (G₁ G₂ K : Subgroup D) : Prop where
  triple : IsGoldschmidtTriple G₁ G₂
  pPrimeCore_eq_bot : CFSG.pPrimeCore 3 D = ⊥
  pCore_eq_bot : Open.pCore 2 D = ⊥
  component : CFSG.IsComponent K
  normal : K.Normal
  le_left : twoResidual G₁ ≤ K
  not_le_right : ¬ twoResidual G₂ ≤ K
  card_left : Nat.card ↥(twoResidual G₁) = 3

namespace Setting

variable {D : Type} [Group D] [Finite D] {G₁ G₂ K : Subgroup D}

theorem sup_eq_top (hS : Setting G₁ G₂ K) : K ⊔ G₂ = ⊤ :=
  sup_eq_top_of_twoResidual_le hS.triple hS.le_left

theorem inf_eq (hS : Setting G₁ G₂ K) :
    G₂ ⊓ K = pCoreOf 2 G₂ ⊓ K ∧ pCoreOf 2 G₂ ⊓ K = G₂ ⊓ G₁ ⊓ K ∧
      IsSylowTwoOf (G₂ ⊓ G₁ ⊓ K) K := by
  have := hS.normal
  exact ((tfae_inf_le_pCoreOf hS.triple.symm isSubnormal_top_of_normal).out 3 2).mp
    hS.not_le_right

theorem isSylowTwoOf_inf (hS : Setting G₁ G₂ K) : IsSylowTwoOf (pCoreOf 2 G₂ ⊓ K) K := by
  obtain ⟨-, e2, hsyl⟩ := hS.inf_eq
  rw [e2]
  exact hsyl

theorem elemAbelian (hS : Setting G₁ G₂ K) :
    IsElemAbelian 2 (pCoreOf 2 G₂) ∧ Nat.card ↥(pCoreOf 2 G₂) ≤ 2 ^ 3 :=
  (f6_13_three hS.triple hS.pCore_eq_bot hS.card_left).1

theorem isPGroup_center (hS : Setting G₁ G₂ K) :
    IsPGroup 3 ↥(Subgroup.center ↥K) :=
  have := hS.normal
  isPGroup_center_of_pPrimeCore_eq_bot hS.pPrimeCore_eq_bot

theorem odd_card_center (hS : Setting G₁ G₂ K) :
    Odd (Nat.card ↥(Subgroup.center ↥K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hS.isPGroup_center.exists_card_eq
  rw [hk]
  exact Odd.pow (by decide)

theorem normal_inf_centralizer (hS : Setting G₁ G₂ K) :
    (K ⊓ Subgroup.centralizer (K : Set D)).Normal := by
  have hKn := hS.normal
  refine ⟨fun z hz g => Subgroup.mem_inf.mpr ⟨hKn.conj_mem z hz.1 g, ?_⟩⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : g⁻¹ * k * g ∈ K := by simpa using hKn.conj_mem k hk g⁻¹
  have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hk'
  calc k * (g * z * g⁻¹) = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ * k := by group

theorem not_le_inf_centralizer (hS : Setting G₁ G₂ K) :
    ¬ twoResidual G₁ ≤ K ⊓ Subgroup.centralizer (K : Set D) := by
  intro hle
  set Z := K ⊓ Subgroup.centralizer (K : Set D) with hZ
  have := hS.normal_inf_centralizer
  have hsup : Z ⊔ G₂ = ⊤ := sup_eq_top_of_twoResidual_le hS.triple hle
  have hZab : Group.IsSolvable ↥Z := Group.isSolvable_of_comm fun a b => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1)
  have : Group.IsSolvable ↥G₂ := isSolvable_vertex_right hS.triple
  have hsurj : Function.Surjective ((QuotientGroup.mk' Z).comp G₂.subtype) := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective Z q
    have hd : d ∈ Z ⊔ G₂ := hsup ▸ Subgroup.mem_top d
    rw [Subgroup.mem_sup_of_normal_left] at hd
    obtain ⟨z, hz, g, hg, rfl⟩ := hd
    refine ⟨⟨g, hg⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have h1 := hS.normal_inf_centralizer.conj_mem z hz g⁻¹
    rw [inv_inv, mul_assoc] at h1
    exact h1
  have : Group.IsSolvable (D ⧸ Z) := Group.isSolvable_of_surjective hsurj
  have : Group.IsSolvable D := Group.isSolvable_of_subgroup_quotient Z
  have : Group.IsPerfect ↥K := hS.component.1.1
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hS.component.1
  exact Group.IsPerfect.not_isSolvable ↥K inferInstance


theorem exists_sylow_eq (hS : Setting G₁ G₂ K) :
    ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K) = (pCoreOf 2 G₂ ⊓ K).subgroupOf K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := hS.isSylowTwoOf_inf
  exact ⟨(hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm).toSylow hsyl.2.2, rfl⟩

theorem four_le_card_inf (hS : Setting G₁ G₂ K) : 4 ≤ Nat.card ↥(pCoreOf 2 G₂ ⊓ K) := by
  have hq : CFSG.IsQuasisimple ↥K := hS.component.1
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2.1
  obtain ⟨P, hP⟩ := hS.exists_sylow_eq
  obtain ⟨Q, ⟨eQ⟩⟩ := exists_sylow_quotient_mulEquiv _ hS.odd_card_center P
  have h4 := (not_isCyclic_sylow_two hq.2.2 Q).2
  have hPQ : Nat.card ↥(P : Subgroup ↥K) = Nat.card ↥(pCoreOf 2 G₂ ⊓ K) := by
    rw [hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← hPQ, Nat.card_congr eQ.toEquiv]
  exact Nat.le_of_dvd Nat.card_pos h4

theorem exists_generator (hS : Setting G₁ G₂ K) :
    ∃ x ∈ twoResidual G₁, orderOf x = 3 ∧ x ∉ Subgroup.centralizer (K : Set D) ∧
      ∀ q ∈ pCoreOf 2 G₂, q * x * q⁻¹ = x ∨ q * x * q⁻¹ = x⁻¹ := by
  have h := hS.triple
  set L₁ := twoResidual G₁ with hL₁
  obtain ⟨x, hxL, hx1⟩ : ∃ x ∈ L₁, x ≠ 1 := by
    by_contra hne
    push Not at hne
    have : L₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hne
    have h3 := hS.card_left
    rw [← hL₁, this, Subgroup.card_bot] at h3
    omega
  have hord : orderOf x = 3 := by
    have h1 : orderOf x ∣ 3 := hS.card_left ▸ Subgroup.orderOf_dvd_natCard L₁ hxL
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.mp h2) hx1
    · exact h2
  refine ⟨x, hxL, hord, fun hxC => ?_, fun q hq => ?_⟩
  ·
    apply hS.not_le_inf_centralizer
    intro y hy
    refine ⟨hS.le_left hy, ?_⟩
    rcases mem_of_card_eq_three hS.card_left hxL hx1 hy with rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hxC
    · exact Subgroup.inv_mem _ hxC
  · have hqT : q ∈ G₁ ⊓ G₂ := pCoreOf_le_inf_right h hq
    have hqN := le_normalizer_twoResidual G₁ (Subgroup.mem_inf.mp hqT).1
    have hmem := (Subgroup.mem_normalizer_iff.mp hqN x).mp hxL
    rcases mem_of_card_eq_three hS.card_left hxL hx1 hmem with h1 | h1 | h1
    · exfalso
      apply hx1
      calc x = q⁻¹ * (q * x * q⁻¹) * q := by group
        _ = 1 := by rw [h1]; group
    · exact Or.inl h1
    · exact Or.inr h1



theorem pCoreOf_inf_centralizer (hS : Setting G₁ G₂ K) :
    pCoreOf 2 G₂ ⊓ Subgroup.centralizer (K : Set D) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hS.triple
  have hCn := normal_centralizer_of_normal hS.normal
  set M := pCoreOf 2 G₂ ⊓ Subgroup.centralizer (K : Set D) with hM
  have hG₂ : G₂ ≤ Subgroup.normalizer (M : Set D) := fun g hg =>
    mem_normalizer_of_forall_conj_mem fun m hm =>
      ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂ hg) m).mp hm.1,
        hCn.conj_mem m hm.2 g⟩
  have hL₁ : twoResidual G₁ ≤ Subgroup.normalizer (M : Set D) := fun l hl =>
    mem_normalizer_of_forall_conj_mem fun m hm => by
      have hc := Subgroup.mem_centralizer_iff.mp hm.2 l (hS.le_left hl)
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      exact hm
  have hMn : M.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff, ← h.gen]
    refine sup_le ?_ hG₂
    rw [← inf_sup_twoResidual_left h]
    exact sup_le (inf_le_right.trans hG₂) hL₁
  have hM2 : IsPGroup 2 M := (pCoreOf_isPGroup 2 G₂).to_le inf_le_left
  have hle := le_pCore 2 hMn hM2
  rw [hS.pCore_eq_bot] at hle
  exact le_bot_iff.mp hle

theorem inf_centralizer_eq_bot (hS : Setting G₁ G₂ K) :
    G₂ ⊓ Subgroup.centralizer (K : Set D) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hS.triple
  have hCn := normal_centralizer_of_normal hS.normal
  set N := G₂ ⊓ Subgroup.centralizer (K : Set D) with hN
  set Q₂ := pCoreOf 2 G₂ with hQ₂
  set L₁ := twoResidual G₁ with hL₁
  by_contra hne
  have hNQ : ¬ N ≤ Q₂ := by
    intro hle
    apply hne
    rw [eq_bot_iff, ← hS.pCoreOf_inf_centralizer]
    exact le_inf hle inf_le_right
  have hNsub : IsSubnormal N G₂ := by
    refine IsSubnormal.step inf_le_left ⟨fun n hn g => ?_⟩ (IsSubnormal.refl G₂)
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨G₂.mul_mem (G₂.mul_mem g.2 hn.1) (G₂.inv_mem g.2), hCn.conj_mem _ hn.2 g⟩
  have hL₂N : twoResidual G₂ ≤ N := twoResidual_le_of_isSubnormal h.symm hNsub hNQ
  obtain ⟨D₂, hD₂, -⟩ := exists_isSylowIn_ge 3 (H := G₂) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  have hD₂C : D₂ ≤ Subgroup.centralizer (K : Set D) := by
    intro d hd
    refine (hL₂N (mem_twoResidual_of_odd (hD₂.1 hd) ?_)).2
    obtain ⟨k, hk⟩ := hD₂.2.1 ⟨d, hd⟩
    have h1 : orderOf d ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    exact Odd.of_dvd_nat (Odd.pow (by decide)) h1
  obtain ⟨x, hxL, hxo, -, hxn⟩ := hS.exists_generator
  have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hxo; norm_num at hxo
  obtain ⟨e, heQK, he1, hex⟩ := exists_ne_one_commute (P := Q₂ ⊓ K)
    (IsElemAbelian.mono hS.elemAbelian.1 inf_le_left) hS.four_le_card_inf fun q hq => hxn q hq.1
  set S := Q₂ ⊓ K ⊓ Subgroup.centralizer (L₁ : Set D) with hSdef
  have heS : e ∈ S := by
    refine ⟨heQK, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rcases mem_of_card_eq_three hS.card_left hxL hx1 hy with rfl | rfl | rfl
    · simp
    · exact hex.symm
    · calc x⁻¹ * e = x⁻¹ * (e * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * e) * x⁻¹ := by rw [hex]
        _ = e * x⁻¹ := by group
  have hSD : D₂ ≤ Subgroup.normalizer (S : Set D) := fun d hd =>
    mem_normalizer_of_forall_conj_mem fun s hs => by
      have hc := Subgroup.mem_centralizer_iff.mp (hD₂C hd) s hs.1.2
      rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
      exact hs
  have hSn : Q₂ ⊔ L₁ ≤ Subgroup.normalizer (S : Set D) := by
    refine sup_le (fun q hq => mem_normalizer_of_forall_conj_mem fun s hs => ?_)
      (fun l hl => mem_normalizer_of_forall_conj_mem fun s hs => ?_)
    · refine ⟨⟨Q₂.mul_mem (Q₂.mul_mem hq hs.1.1) (Q₂.inv_mem hq),
        hS.normal.conj_mem s hs.1.2 q⟩, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      have hqT : q ∈ G₁ ⊓ G₂ := pCoreOf_le_inf_right h hq
      have hqN := le_normalizer_twoResidual G₁ (G₁.inv_mem (Subgroup.mem_inf.mp hqT).1)
      have hl' : q⁻¹ * l * q⁻¹⁻¹ ∈ L₁ := (Subgroup.mem_normalizer_iff.mp hqN l).mp hl
      rw [inv_inv] at hl'
      have hc := Subgroup.mem_centralizer_iff.mp hs.2 _ hl'
      calc l * (q * s * q⁻¹) = q * ((q⁻¹ * l * q) * s) * q⁻¹ := by group
        _ = q * (s * (q⁻¹ * l * q)) * q⁻¹ := by rw [hc]
        _ = q * s * q⁻¹ * l := by group
    · have hc := Subgroup.mem_centralizer_iff.mp hs.2 l hl
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      exact hs
  have hS0 := eq_bot_of_le_pCoreOf_of_normalizes h hS.pCore_eq_bot hD₂
    (inf_le_left.trans inf_le_left) hSD hSn
  have he0 : e ∈ (⊥ : Subgroup D) := by
    rw [← hS0]
    exact heS
  exact he1 (Subgroup.mem_bot.mp he0)


theorem odd_card_centralizer (hS : Setting G₁ G₂ K) :
    Odd (Nat.card (Subgroup.centralizer (K : Set D))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hS.triple
  have hCn := normal_centralizer_of_normal hS.normal
  set C := Subgroup.centralizer (K : Set D) with hC
  have hsyl := isSylowIn_inf_of_isSubnormal (X := C) isSubnormal_top_of_normal
    (isSylowTwoOf_inf_top h)
  have hTC : G₁ ⊓ G₂ ⊓ C = ⊥ := by
    rw [eq_bot_iff, ← hS.inf_centralizer_eq_bot]
    exact inf_le_inf_right C inf_le_right
  have h2 := hsyl.2.2
  rw [hTC, Subgroup.relIndex, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h2
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)

theorem centralizer_le_twoResidual (hS : Setting G₁ G₂ K) :
    Subgroup.centralizer (K : Set D) ≤ twoResidual ⊤ := fun c hc =>
  mem_twoResidual_of_odd (Subgroup.mem_top c)
    (Odd.of_dvd_nat hS.odd_card_centralizer (Subgroup.orderOf_dvd_natCard _ hc))


theorem twoLocalPrimeRank_le_evenRank {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.twoLocalPrimeRank p X ≤ CFSG.Open.evenRank X := by
  refine csSup_le' ?_
  rintro _ ⟨H, hH, rfl⟩
  exact le_csSup ⟨Nat.card X, by
    rintro _ ⟨q, L, hq, -, -, rfl⟩
    exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt L⟩ ⟨p, H, hp, hp2, hH, rfl⟩

theorem exists_psl2
    (hW : WalterModelsStatement) (hS : Setting G₁ G₂ K)
    (hqt : CFSG.Open.evenRank (↥K ⧸ Subgroup.center ↥K) ≤ 2) :
    ∃ (p f : ℕ) (F : Type) (_ : Field F) (_ : Finite F), p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nat.card F = p ^ f ∧ IsL2 p f ↥K ∧
      Nonempty (↥K ≃* Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSL 2 F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKn := hS.normal
  have hq : CFSG.IsQuasisimple ↥K := hS.component.1
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2.1
  have hnonab : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a := hq.2.2
  have : Group.IsPerfect ↥K := hq.1
  set π := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  obtain ⟨P, hP⟩ := hS.exists_sylow_eq
  obtain ⟨hEA, hQ8⟩ := hS.elemAbelian
  have hPmem : ∀ y : ↥K, y ∈ (P : Subgroup ↥K) ↔ (y : D) ∈ pCoreOf 2 G₂ := by
    intro y
    rw [hP, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
  have hinj : Function.Injective (π.comp (P : Subgroup ↥K).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hy
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := P.isPGroup' y
    have h1 : orderOf (y : ↥K) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf (y : ↥K) ∣ Nat.card ↥(Subgroup.center ↥K) :=
      Subgroup.orderOf_dvd_natCard _ hy
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(Subgroup.center ↥K)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hS.odd_card_center)
    exact Subtype.ext (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2))
  set Q : Sylow 2 (↥K ⧸ Subgroup.center ↥K) := P.mapSurjective (QuotientGroup.mk'_surjective _)
    with hQdef
  have hQ : (Q : Subgroup (↥K ⧸ Subgroup.center ↥K)) = (P : Subgroup ↥K).map π := by
    rw [hQdef, Sylow.coe_mapSurjective]
  let ψ : ↥(P : Subgroup ↥K) ≃* ↥(Q : Subgroup (↥K ⧸ Subgroup.center ↥K)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (by
      rw [hQ, MonoidHom.range_comp, Subgroup.range_subtype]))
  have hcardPQ : Nat.card ↥(P : Subgroup ↥K) =
      Nat.card ↥(Q : Subgroup (↥K ⧸ Subgroup.center ↥K)) :=
    Nat.card_congr ψ.toEquiv
  have hPQ2 : Nat.card ↥(P : Subgroup ↥K) = Nat.card ↥(pCoreOf 2 G₂ ⊓ K) := by
    rw [hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hQle8 : Nat.card ↥(Q : Subgroup (↥K ⧸ Subgroup.center ↥K)) ≤ 8 := by
    rw [← hcardPQ, hPQ2]
    exact (Subgroup.card_le_of_le inf_le_left).trans hQ8
  have h4 := (not_isCyclic_sylow_two hnonab Q).2
  have hQ4 : 4 ≤ Nat.card ↥(Q : Subgroup (↥K ⧸ Subgroup.center ↥K)) :=
    Nat.le_of_dvd Nat.card_pos h4
  have hQmem : ∀ z ∈ (Q : Subgroup (↥K ⧸ Subgroup.center ↥K)), ∃ y : ↥K,
      (y : D) ∈ pCoreOf 2 G₂ ∧ π y = z := by
    intro z hz
    rw [hQ] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨y, (hPmem y).mp hy, rfl⟩
  have hQsq : ∀ z ∈ (Q : Subgroup (↥K ⧸ Subgroup.center ↥K)), z * z = 1 := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hQmem z hz
    rw [← map_mul, ← pow_two]
    have : y ^ 2 = 1 := Subtype.ext (by simpa using hEA.2 _ hy)
    rw [this, map_one]
  have hQab : IsMulCommutative (Q : Subgroup (↥K ⧸ Subgroup.center ↥K)) := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨y, hy, hya⟩ := hQmem a a.2
    obtain ⟨y', hy', hyb⟩ := hQmem b b.2
    change (a : ↥K ⧸ Subgroup.center ↥K) * b = b * a
    rw [← hya, ← hyb, ← map_mul, ← map_mul]
    congr 1
    have hc := hEA.1.is_comm.comm (⟨(y : D), hy⟩ : ↥(pCoreOf 2 G₂)) ⟨(y' : D), hy'⟩
    exact Subtype.ext (congrArg (Subtype.val : ↥(pCoreOf 2 G₂) → D) hc)
  obtain ⟨x, hxL, hxo, hxC, hxn⟩ := hS.exists_generator
  set xK : ↥K := ⟨x, hS.le_left hxL⟩ with hxK
  have hxbar : orderOf (π xK) = 3 := by
    refine orderOf_eq_prime ?_ fun h1 => hxC ?_
    · rw [← map_pow]
      have : xK ^ 3 = 1 := Subtype.ext (by simpa [hxK] using hxo ▸ pow_orderOf_eq_one x)
      rw [this, map_one]
    · rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at h1
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact congrArg Subtype.val (h1 ⟨k, hk⟩)
  have hQn : ∀ z ∈ (Q : Subgroup (↥K ⧸ Subgroup.center ↥K)),
      z * π xK * z⁻¹ = π xK ∨ z * π xK * z⁻¹ = (π xK)⁻¹ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hQmem z hz
    rcases hxn _ hy with h1 | h1
    · left
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h1
    · right
      rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
      congr 1
      exact Subtype.ext h1
  rcases hW (↥K ⧸ Subgroup.center ↥K) hnonab Q hQab with ⟨f, hf, hm⟩ |
      ⟨p, f, hp, hp2, hf, hq5, h8, hm⟩ | ⟨f, -, hf3, hm⟩ | hJ
  ·
    exfalso
    obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
    obtain ⟨e, heQ, he1, hex⟩ := exists_ne_one_commute (x := π xK)
      (P := (Q : Subgroup (↥K ⧸ Subgroup.center ↥K)))
      ⟨hQab, fun z hz => by rw [pow_two]; exact hQsq z hz⟩ hQ4 hQn
    let ε : ↥K ⧸ Subgroup.center ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
      eF.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
    have heo : orderOf (ε e) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact hQsq e heQ) he1
    have hxo' : orderOf (ε (π xK)) = 3 := by rw [MulEquiv.orderOf_eq, hxbar]
    have hc : Commute (ε e) (ε (π xK)) := by
      change ε e * ε (π xK) = ε (π xK) * ε e
      rw [← map_mul, ← map_mul, hex]
    exact CFSG.GorensteinWalter.psl2_no_commuting_distinct_prime_order (r := 2) (p := 3) hF
      (by norm_num) heo hxo' hc
  ·
    obtain ⟨hadm, F, _, _, hF, ⟨eF⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
    have : Fact p.Prime := ⟨hp⟩
    have hZ : Subgroup.center ↥K = ⊥ := (center_of_quotient_psl_two hS.isPGroup_center hp2 hF
      eF).1 (by intro h9; rw [h9] at h8; norm_num at h8)
    let eK : ↥K ≃* Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSL 2 F) :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans eF
    exact ⟨p, f, F, inferInstance, inferInstance, hp, hp2, hf, hq5, h8, hF,
      ⟨hadm, F, inferInstance, inferInstance, hF, ⟨eK⟩⟩, ⟨eK⟩⟩
  ·
    exfalso
    have hree : CFSG.Blueprint.ReeTitsModel (↥K ⧸ Subgroup.center ↥K) .twistedG2 3 f := by
      rcases hm with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact h
      · exact absurd h (by decide)
    have h3 := CFSG.SectionRank.QTK.three_le_localRank_of_smallReeModel hree
    have h4 := twoLocalPrimeRank_le_evenRank (X := ↥K ⧸ Subgroup.center ↥K) Nat.prime_three
      (by norm_num)
    have h5 : CFSG.Assembly.RankThreeEven.localRank 3 (↥K ⧸ Subgroup.center ↥K) ≤ 2 :=
      h4.trans hqt
    omega
  ·
    exfalso
    obtain ⟨eJ⟩ := hJ
    let ε : ↥K ⧸ Subgroup.center ↥K ≃* CFSG.Open.walterJ1 :=
      eJ.trans CFSG.Walter.walterJ1EquivNative.symm
    obtain ⟨Q', ⟨ι⟩⟩ := exists_sylow_mulEquiv_of_mulEquiv ε Q
    have hQ'8 := (CFSG.Walter.J1Props.jankoHyp.sylow_structure Q').1
    have hQcard : Nat.card ↥(Q : Subgroup (↥K ⧸ Subgroup.center ↥K)) = 8 := by
      rw [Nat.card_congr ι.toEquiv, hQ'8]
    set y := ε (π xK) with hy
    have hyo : orderOf y = 3 := by rw [hy, MulEquiv.orderOf_eq, hxbar]
    have hY3 : Nat.card ↥(Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hyo]
    have hJcard := CFSG.Walter.J1Props.J1_card
    let P₃ : Sylow 3 CFSG.Open.walterJ1 := Sylow.ofCard (Subgroup.zpowers y) (by
      rw [hY3, hJcard]
      have : (2 ^ 3 * 3 * 5 * 7 * 11 * 19 : ℕ) = 3 ^ 1 * 58520 := by norm_num
      rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      norm_num)
    have hN := CFSG.Walter.J1Props.J2_normalizer_two_part (p := 3) (Or.inl rfl) P₃
    have hle : (Q : Subgroup (↥K ⧸ Subgroup.center ↥K)).map ε.toMonoidHom ≤
        Subgroup.normalizer ((P₃ : Subgroup CFSG.Open.walterJ1) : Set CFSG.Open.walterJ1) := by
      rintro _ ⟨z, hz, rfl⟩
      refine mem_normalizer_of_forall_conj_mem fun w hw => ?_
      change w ∈ Subgroup.zpowers y at hw
      change ε z * w * (ε z)⁻¹ ∈ Subgroup.zpowers y
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← conj_zpow]
      refine Subgroup.zpow_mem _ ?_ k
      rcases hQn z hz with h1 | h1
      · rw [hy, ← map_inv, ← map_mul, ← map_mul, h1]
        exact Subgroup.mem_zpowers _
      · rw [hy, ← map_inv, ← map_mul, ← map_mul, h1, map_inv]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    have h8 : 2 ^ 3 ∣ Nat.card ↥(Subgroup.normalizer
        ((P₃ : Subgroup CFSG.Open.walterJ1) : Set CFSG.Open.walterJ1)) := by
      have h1 := Subgroup.card_dvd_of_le hle
      rwa [Subgroup.card_map_of_injective ε.injective, hQcard] at h1
    have h3 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h8
    omega

end Setting

end CFSG.Quasithin.RonanF617
