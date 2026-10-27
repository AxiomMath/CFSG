module

public import CFSG.Quasithin.H13.A5S136sp1
public import CFSG.Quasithin.H13.A5S136sp5
public import CFSG.Quasithin.H13.A5S136sp8
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Main
public import CFSG.Quasithin.H13.A5S136sz2
public import CFSG.Quasithin.H13.A5S136sp4

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Assembly.LowTwoRank
open CFSG.Blueprint CFSG.SectionRank

@[expose] def stabE12 : Subgroup (Equiv.Perm (Fin 5)) where
  carrier := {σ | pact σ E12 = E12}
  one_mem' := by simp
  mul_mem' := fun {σ τ} hσ hτ => by
    show pact (σ * τ) E12 = E12
    rw [map_mul, MulAut.mul_apply, show pact τ E12 = E12 from hτ, show pact σ E12 = E12 from hσ]
  inv_mem' := fun {σ} hσ => by
    show pact σ⁻¹ E12 = E12
    have h : pact σ E12 = E12 := hσ
    rw [map_inv, MulAut.inv_apply, MulEquiv.symm_apply_eq, h]

theorem card_stabE12 : Nat.card stabE12 = 12 := by
  have : Fintype.card {σ : Equiv.Perm (Fin 5) // pact σ E12 = E12} = 12 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem card_stabE12_cube :
    Fintype.card {σ : Equiv.Perm (Fin 5) // pact σ E12 = E12 ∧ σ ^ 3 = 1} = 3 := by
  decide +kernel

namespace ConfSp

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_inner_of_indHom {K : Subgroup G} (hO2 : CFSG.pCore 2 ↥K = ⊥) {l : G}
    (hlN : l ∈ Subgroup.normalizer (K : Set G)) {k : ↥K ⧸ CFSG.pCore 2 ↥K}
    (hk : ConfAB.indHom K (MulEquiv.refl _) ⟨l, hlN⟩ = MulAut.conj k) :
    ∃ k₀ ∈ K, ∀ x ∈ K, l * x * l⁻¹ = k₀ * x * k₀⁻¹ := by
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective k
  refine ⟨k₀, k₀.2, fun x hx => ?_⟩
  have hinj : Function.Injective (QuotientGroup.mk : ↥K → ↥K ⧸ CFSG.pCore 2 ↥K) := by
    intro a b hab
    rw [QuotientGroup.eq, hO2, Subgroup.mem_bot] at hab
    exact (inv_mul_eq_one.mp hab)
  have h1 := DFunLike.congr_fun hk (QuotientGroup.mk ⟨x, hx⟩)
  have h2 := ConfAB.indHom_apply K (MulEquiv.refl _) ⟨l, hlN⟩ ⟨x, hx⟩
  simp only [MulEquiv.refl_apply] at h2
  rw [h2, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul] at h1
  have h3 := congrArg Subtype.val (hinj h1)
  simpa using h3

omit [Finite G] in
theorem conj_injective {K : Subgroup G} (hZ : ∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x = 1) :
    Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  apply Subtype.ext
  refine hZ k k.2 fun y hy => ?_
  have h1 := congrArg Subtype.val (DFunLike.congr_fun hk ⟨y, hy⟩)
  have h2 : (k : G) * y * (k : G)⁻¹ = y := by simpa [MulAut.conj_apply] using h1
  calc (k : G) * y = (k : G) * y * (k : G)⁻¹ * k := by group
    _ = y * k := by rw [h2]

omit [Finite G] in
theorem comm_mem_centralizer {K : Subgroup G} {y z : G} (hinner : Ch1.InducesInner z K)
    (hyc : ∀ x ∈ K, y * x * y⁻¹ = x) : y * z * y⁻¹ * z⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  obtain ⟨l, hlK, hl⟩ := hinner
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  set x₁ := l⁻¹ * x * l with hx₁
  have hx₁K : x₁ ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hlK) hx) hlK
  have e0 : z⁻¹ * x * z = x₁ := hl x hx
  have e1 : z⁻¹ * x = x₁ * z⁻¹ := by rw [← e0]; group
  have e2 : y⁻¹ * x₁ = x₁ * y⁻¹ := by
    have := hyc x₁ hx₁K
    calc y⁻¹ * x₁ = y⁻¹ * (y * x₁ * y⁻¹) := by rw [this]
      _ = x₁ * y⁻¹ := by group
  have e3 : z * x₁ = x * z := by rw [← e0]; group
  have e4 : y * x = x * y := by
    have := hyc x hx
    calc y * x = y * x * y⁻¹ * y := by group
      _ = x * y := by rw [this]
  calc x * (y * z * y⁻¹ * z⁻¹) = (x * y) * z * y⁻¹ * z⁻¹ := by group
    _ = (y * x) * z * y⁻¹ * z⁻¹ := by rw [e4]
    _ = y * (x * z) * y⁻¹ * z⁻¹ := by group
    _ = y * (z * x₁) * y⁻¹ * z⁻¹ := by rw [e3]
    _ = y * z * (x₁ * y⁻¹) * z⁻¹ := by group
    _ = y * z * (y⁻¹ * x₁) * z⁻¹ := by rw [e2]
    _ = y * z * y⁻¹ * (x₁ * z⁻¹) := by group
    _ = y * z * y⁻¹ * (z⁻¹ * x) := by rw [e1]
    _ = y * z * y⁻¹ * z⁻¹ * x := by group

end ConfSp

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem card_primes_of_le {W : Subgroup G} (hWLT : W ≤ L ⊔ T)
    (hWV : W ≤ Subgroup.normalizer (V : Set G))
    (hWv : W ≤ Subgroup.centralizer ({S.v12} : Set G)) :
    (∀ p : ℕ, p.Prime → p ∣ Nat.card W → p = 2 ∨ p = 3) ∧ ¬ 9 ∣ Nat.card W := by
  let ρW : ↥W →* Equiv.Perm (Fin 5) := S.frame.ρ.comp (Subgroup.inclusion hWV)
  have hker : IsPGroup 2 ρW.ker := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
      rw [S.cLT]
      exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)
    rintro ⟨w, hw⟩
    have hwC : ((w : ↥W) : G) ∈ Subgroup.centralizer (V : Set G) :=
      S.frame.mem_centralizer_of_rho (Subgroup.inclusion hWV w) (MonoidHom.mem_ker.mp hw)
    obtain ⟨k, hk⟩ := h1 ⟨(w : G), Subgroup.mem_inf.mpr ⟨hWLT w.2, hwC⟩⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hrange : ρW.range ≤ stabE12 := by
    rintro _ ⟨w, rfl⟩
    have h1 : (w : G) * S.v12 * (w : G)⁻¹ = S.v12 := by
      have := hWv w.2
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      rw [this]
      group
    have h2 := (S.conj_eq_iff (Subgroup.inclusion hWV w) ⟨S.v12, S.v12_mem_V⟩).1 h1
    rw [S.psi_v12] at h2
    exact h2
  have hcard : Nat.card ↥W = Nat.card ρW.ker * Nat.card ρW.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρW).toEquiv, mul_comm,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hker
  have hr12 : Nat.card ρW.range ∣ 12 := card_stabE12 ▸ Subgroup.card_dvd_of_le hrange
  rw [hcard, ha]
  refine ⟨fun p hp hpd => ?_, fun h9 => ?_⟩
  · rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · have h12 := h.trans hr12
      have : p ∣ 2 ^ 2 * 3 := h12
      rcases (Nat.Prime.dvd_mul hp).mp this with h' | h'
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h'))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h')
  · have hcop : Nat.Coprime 9 (2 ^ a) :=
      Nat.Coprime.pow_right a (by norm_num)
    have h1 : 9 ∣ Nat.card ρW.range := hcop.dvd_of_dvd_mul_left h9
    have h2 := h1.trans hr12
    omega

end Setting

theorem elim1366Sp4_of (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) : Elim1366Sp4 := by
  intro G _ _ T L V S _ K hK hn hsimp hPq hinner hLv
  obtain ⟨f, hf, hPq⟩ := hPq
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hqs : CFSG.IsQuasisimple ↥K :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hK.1)).1 hK.2.1
  have hO2 := ConfAB.pCore_two_eq_bot_of_simple hqs hsimp
  let ψ₀ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot
  have hX : StatedClassicalModel ↥K .PSp 2 2 f := statedClassicalModel_of_mulEquiv ψ₀.symm hPq
  have hZK := ConfAB.center_eq_bot_of_simple hqs hsimp
  have hZ : ∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x = 1 := by
    intro x hx hc
    have hxZ : (⟨x, hx⟩ : ↥K) ∈ Subgroup.center ↥K :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2).symm
    rw [hZK, Subgroup.mem_bot] at hxZ
    exact congrArg Subtype.val hxZ
  have hconj := ConfSp.conj_injective hZ
  have hTv := S.isSylowTwoOf_Tv h1222 h517
  have hT2 : IsPGroup 2 S.Tv := hTv.2.1
  have hGvN : Gv ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK.1).mp hn
  have hTN : S.Tv ≤ Subgroup.normalizer (K : Set G) := S.Tv_le_Gv.trans hGvN
  have hsyl : IsSylowTwoOf (S.Tv ⊓ K) K := A4.isSylowTwoOf_inf_normal hTv hK.1 hGvN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ((S.Tv ⊓ K).subgroupOf K) :=
    hsyl.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.le).symm
  let P : Sylow 2 ↥K := hS2.toSylow hsyl.2.2
  have hP : ∀ x : ↥K, x ∈ (P : Subgroup ↥K) ↔ (x : G) ∈ S.Tv ⊓ K := fun x => Iff.rfl
  have hNP : ∀ b : ↥K, b ∈ Subgroup.normalizer ((P : Subgroup ↥K) : Set ↥K) ↔
      (b : G) ∈ Subgroup.normalizer ((S.Tv ⊓ K : Subgroup G) : Set G) := by
    intro b
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hb x
      by_cases hx : x ∈ K
      · have h1 := hb ⟨x, hx⟩
        rw [hP, hP] at h1
        exact h1
      · have h1 : x ∉ S.Tv ⊓ K := fun h => hx (Subgroup.mem_inf.mp h).2
        have h2 : (b : G) * x * (b : G)⁻¹ ∉ S.Tv ⊓ K := fun h => hx (by
          have := SzPair.conj_inv_mem_of_mem_normalizer (Subgroup.le_normalizer b.2)
            (Subgroup.mem_inf.mp h).2
          simpa [mul_assoc] using this)
        exact iff_of_false h1 h2
    · intro hb x
      rw [hP, hP]
      exact hb x
  have hF1 := SpBorel.clause1 hf hX P
  have hF3 := SpBorel.clause3 hf hX P
  have hF4' := SpBorel.clause4 hf hX P
  have hF5 := SpBorel.clause5 hf hX P
  have hUmem : ∀ u : ↥K, u ∈ omegaOneCenterOf (P : Subgroup ↥K) →
      (u : G) ∈ omegaOneCenterOf (S.Tv ⊓ K) := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx.1
      refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨(hP x).1 hxP, ?_⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyK : y ∈ K := (Subgroup.mem_inf.mp hy).2
        exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxC ⟨y, hyK⟩ ((hP _).2 hy))
      · simpa using congrArg Subtype.val hx.2
    | one => exact Subgroup.one_mem _
    | mul x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => exact Subgroup.inv_mem _ hx
  have hTvP : ∀ s ∈ S.Tv, s ∈ Subgroup.normalizer ((S.Tv ⊓ K : Subgroup G) : Set G) :=
    fun s hs => ConfSz.mem_normalizer_inf (Subgroup.le_normalizer hs) (hTN hs)
  have hinn : ∀ s ∈ S.Tv, (∀ u ∈ omegaOneCenterOf (S.Tv ⊓ K), s * u * s⁻¹ = u) →
      ∃ k ∈ K, ∀ x ∈ K, s * x * s⁻¹ = k * x * k⁻¹ := by
    intro s hs hsU
    have hαP : ∀ x ∈ (P : Subgroup ↥K),
        K.normalizerMonoidHom ⟨s, hTN hs⟩ x ∈ (P : Subgroup ↥K) := by
      intro x hx
      rw [hP]
      exact SzPair.conj_mem_of_mem_normalizer (hTvP s hs) ((hP x).1 hx)
    have hαU : ∀ u ∈ omegaOneCenterOf (P : Subgroup ↥K),
        K.normalizerMonoidHom ⟨s, hTN hs⟩ u = u :=
      fun u hu => Subtype.ext (hsU _ (hUmem u hu))
    obtain ⟨g, hg⟩ := hF1 _ hαP hαU
    refine ⟨g, g.2, fun x hx => ?_⟩
    have := congrArg Subtype.val (DFunLike.congr_fun hg ⟨x, hx⟩)
    simpa [MulAut.conj_apply] using this.symm
  have hJ : thompsonJ S.Tv ≤
      S.Tv ⊓ Subgroup.centralizer (omegaOneCenterOf (S.Tv ⊓ K) : Set G) := by
    refine (thompsonJ_le_innerPart_sp4 hf hX hsyl hT2 hTN).trans (sup_le ?_ ?_)
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
        Subgroup.mem_centralizer_iff.mpr fun u hu => SpComp.omegaOneCenter_comm _ hu hx⟩
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
        Subgroup.mem_centralizer_iff.mpr fun u hu =>
          Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 u
            (Subgroup.mem_inf.mp (SpComp.omegaOneCenter_le _ hu)).2⟩
  have hB : ∀ b ∈ K, b ∈ Subgroup.normalizer ((S.Tv ⊓ K : Subgroup G) : Set G) →
      b ∈ Subgroup.normalizer (V : Set G) ∧ b ∈ Gv := by
    intro b hbK hbN
    have h1 := SpComp.mem_normalizer_baum_of_le hT2 hTN hsyl hZ hinn hJ hbK hbN
    rw [show baum S.Tv = baum T from S.lemma_13_6_4.1] at h1
    exact Subgroup.mem_inf.mp (S.lemma_13_6_5 h1222 h517 (Subgroup.mem_inf.mpr ⟨hK.1 hbK, h1⟩))
  obtain ⟨X, Q, y, hyLv, hconf⟩ := S.exists_conf1366_Lv h1222 h517 h37 h38 hK hinner
  have hyodd : Odd (orderOf y) := hconf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hyz := hconf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hy3 : y ^ 3 = 1 := S.pow_three_eq_one_of_mem_Lv hyLv hyodd
  have hLvN : S.Lv ≤ Subgroup.normalizer (K : Set G) := S.Lv_le_Gv.trans hGvN
  set W := S.Lv ⊔ (S.Tv ⊓ K) with hW
  have hWN : W ≤ Subgroup.normalizer (K : Set G) :=
    sup_le hLvN (inf_le_right.trans Subgroup.le_normalizer)
  let φ : ↥W →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hWN)
  have hφ : ∀ (w : ↥W) (x : ↥K), ((φ w x : ↥K) : G) = w * x * (w : G)⁻¹ := fun _ _ => rfl
  have hφin : ∀ w : ↥W, ∃ k : ↥K, MulAut.conj k = φ w := by
    let I : Subgroup G :=
      ((CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K).comap
        K.normalizerMonoidHom).map (Subgroup.normalizer (K : Set G)).subtype
    have hI : ∀ g (hg : g ∈ Subgroup.normalizer (K : Set G)) (k : ↥K),
        (∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹) → g ∈ I := by
      intro g hg k hk
      refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩, Subgroup.mem_comap.mpr
        (MonoidHom.mem_range.mpr ⟨k, MulEquiv.ext fun x => Subtype.ext ?_⟩), rfl⟩
      simp [MulAut.conj_apply, hk x x.2]
    have hWI : W ≤ I := by
      refine sup_le (fun l hl => ?_) (fun p hp => ?_)
      · obtain ⟨k, hk⟩ := hLv l hl (hLvN hl)
        obtain ⟨k₀, hk₀K, hk₀⟩ := ConfSp.exists_inner_of_indHom hO2 (hLvN hl) hk
        exact hI l (hLvN hl) ⟨k₀, hk₀K⟩ hk₀
      · exact hI p (Subgroup.le_normalizer (Subgroup.mem_inf.mp hp).2)
          ⟨p, (Subgroup.mem_inf.mp hp).2⟩ fun x _ => rfl
    intro w
    obtain ⟨⟨g, hg⟩, hgI, hgw⟩ := Subgroup.mem_map.mp (hWI w.2)
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (Subgroup.mem_comap.mp hgI)
    exact ⟨k, hk.trans (congrArg K.normalizerMonoidHom (Subtype.ext hgw))⟩
  let H : Subgroup ↥K := φ.range.comap MulAut.conj
  have hPH : (P : Subgroup ↥K) ≤ H := by
    intro p hp
    refine ⟨⟨(p : G), Subgroup.mem_sup_right ((hP p).1 hp)⟩, MulEquiv.ext fun x => ?_⟩
    apply Subtype.ext
    rw [hφ]
    rfl
  have hHcard : Nat.card H = Nat.card φ.range := by
    refine Nat.card_congr (Equiv.ofBijective (fun k : ↥H => (⟨MulAut.conj (k : ↥K), k.2⟩ :
      ↥φ.range)) ⟨fun a b hab => Subtype.ext (hconj (congrArg Subtype.val hab)), ?_⟩)
    rintro ⟨_, ⟨w, rfl⟩⟩
    obtain ⟨k, hk⟩ := hφin w
    exact ⟨⟨k, show MulAut.conj k ∈ φ.range from hk ▸ ⟨w, rfl⟩⟩, Subtype.ext hk⟩
  have hWcard : Nat.card φ.range ∣ Nat.card ↥W := by
    have h1 : Nat.card ↥W = Nat.card φ.ker * Nat.card φ.range := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm,
        ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    rw [h1]
    exact dvd_mul_left _ _
  have hWprimes := S.card_primes_of_le (W := W)
    (sup_le ((oTwoRes_le _).trans (inf_le_left.trans le_sup_left))
      (inf_le_left.trans ((inf_le_left (a := T)).trans le_sup_right)))
    (sup_le (fun l hl => S.frame.L_le (oTwoRes_le _ hl).1)
      (inf_le_left.trans ((inf_le_left (a := T)).trans S.frame.T_le)))
    (sup_le S.Lv_le_Gv (inf_le_left.trans S.Tv_le_Gv))
  have hHN : H ≤ Subgroup.normalizer ((P : Subgroup ↥K) : Set ↥K) := by
    refine hF3 H hPH (fun p hp hpd => hWprimes.1 p hp ?_) (fun h9 => hWprimes.2 ?_)
    · rw [hHcard] at hpd
      exact hpd.trans hWcard
    · rw [hHcard] at h9
      exact h9.trans hWcard
  have hyW : y ∈ W := Subgroup.mem_sup_left hyLv
  obtain ⟨k, hk⟩ := hφin ⟨y, hyW⟩
  have hkH : k ∈ H := show MulAut.conj k ∈ φ.range from hk ▸ ⟨⟨y, hyW⟩, rfl⟩
  have hkN := hHN hkH
  have hky : ∀ x ∈ K, y * x * y⁻¹ = (k : G) * x * (k : G)⁻¹ := by
    intro x hx
    have := congrArg Subtype.val (DFunLike.congr_fun hk ⟨x, hx⟩)
    rw [hφ] at this
    simpa [MulAut.conj_apply] using this.symm
  have hk3 : k ^ 3 = 1 := by
    apply hconj
    rw [map_pow, hk, ← map_pow, map_one]
    have : (⟨y, hyW⟩ : ↥W) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply hyz
    refine ConfSp.comm_mem_centralizer hinner fun x hx => ?_
    rw [hky x hx]
    simp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkord : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  have h3B : 3 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup ↥K) : Set ↥K)) := by
    have := orderOf_dvd_natCard (⟨k, hkN⟩ : ↥(Subgroup.normalizer ((P : Subgroup ↥K) : Set ↥K)))
    rwa [Subgroup.orderOf_mk, hkord] at this
  obtain ⟨E₉, hE₉N, hE₉e, hE₉c⟩ := hF4' h3B
  have hEB : ∀ e ∈ E₉, ((e : ↥K) : G) ∈ Subgroup.normalizer (V : Set G) ∧ ((e : ↥K) : G) ∈ Gv :=
    fun e he => hB _ e.2 ((hNP e).1 (hE₉N he))
  let _ := Fintype.ofFinite ↥E₉
  let F : ↥E₉ → {σ : Equiv.Perm (Fin 5) // pact σ E12 = E12 ∧ σ ^ 3 = 1} := fun e =>
    ⟨S.frame.ρ ⟨((e : ↥K) : G), (hEB e e.2).1⟩, by
      refine ⟨?_, ?_⟩
      · have h1 : ((e : ↥K) : G) * S.v12 * ((e : ↥K) : G)⁻¹ = S.v12 := by
          have := (hEB e e.2).2
          rw [Subgroup.mem_centralizer_singleton_iff] at this
          rw [this]
          group
        have h2 := (S.conj_eq_iff ⟨_, (hEB e e.2).1⟩ ⟨S.v12, S.v12_mem_V⟩).1 h1
        rwa [S.psi_v12] at h2
      · rw [← map_pow]
        have : (⟨((e : ↥K) : G), (hEB e e.2).1⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 3 = 1 :=
          Subtype.ext (by simpa using congrArg Subtype.val (hE₉e.2 _ e.2))
        rw [this, map_one]⟩
  obtain ⟨e, e', hee, hFe⟩ := Fintype.exists_ne_map_eq_of_card_lt F (by
    rw [card_stabE12_cube, ← Nat.card_eq_fintype_card, hE₉c]
    norm_num)
  set h : ↥K := (e : ↥K) * (e' : ↥K)⁻¹ with hh
  have hhE : h ∈ E₉ := E₉.mul_mem e.2 (E₉.inv_mem e'.2)
  have hh1 : h ≠ 1 := fun h1 => hee (Subtype.ext (mul_inv_eq_one.mp h1))
  have hh3 : h ^ 3 = 1 := hE₉e.2 h hhE
  have hhB := hEB h hhE
  have hhC : ((h : ↥K) : G) ∈ Subgroup.centralizer (V : Set G) := by
    refine S.frame.mem_centralizer_of_rho ⟨_, hhB.1⟩ ?_
    have h1 := congrArg Subtype.val hFe
    have h2 : (⟨((h : ↥K) : G), hhB.1⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨((e : ↥K) : G), (hEB e e.2).1⟩ * (⟨((e' : ↥K) : G), (hEB e' e'.2).1⟩)⁻¹ :=
      Subtype.ext (by simp [hh])
    rw [h2, map_mul, map_inv]
    exact mul_inv_eq_one.mpr h1
  obtain ⟨t₀, ht₀TL, hρt₀⟩ := S.K4_TL pa (by decide)
  have ht₀v : (t₀ : G) ∈ S.Tv := by
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp ht₀TL).1, ?_⟩
    have h1 := (S.conj_eq_iff t₀ ⟨S.v12, S.v12_mem_V⟩).2 (by rw [hρt₀, S.psi_v12]; decide)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (t₀ : G) * S.v12 = (t₀ : G) * S.v12 * (t₀ : G)⁻¹ * t₀ := by group
      _ = S.v12 * t₀ := by rw [h1]
  set α₀ := K.normalizerMonoidHom ⟨(t₀ : G), hTN ht₀v⟩ with hα₀
  have hα₀app : ∀ x : ↥K, ((α₀ x : ↥K) : G) = t₀ * x * (t₀ : G)⁻¹ := fun _ => rfl
  have hα₀P : ∀ x ∈ (P : Subgroup ↥K), α₀ x ∈ (P : Subgroup ↥K) := by
    intro x hx
    rw [hP, hα₀app]
    exact SzPair.conj_mem_of_mem_normalizer (hTvP _ ht₀v) ((hP x).1 hx)
  have hinv : α₀ k * k ∈ (P : Subgroup ↥K) := by
    obtain ⟨j, hj⟩ := S.two_pow_conj_mul t₀ ht₀v hρt₀ hyLv
    have hwLv : (t₀ : G) * y * (t₀ : G)⁻¹ * y ∈ S.Lv :=
      S.Lv.mul_mem (SzPair.conj_mem_of_mem_normalizer (S.Tv_le_normalizer_Lv ht₀v) hyLv) hyLv
    have hwW : (t₀ : G) * y * (t₀ : G)⁻¹ * y ∈ W := Subgroup.mem_sup_left hwLv
    have hconjw : MulAut.conj (α₀ k * k) = φ ⟨_, hwW⟩ := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [hφ]
      show ((α₀ k : ↥K) : G) * k * x * (((α₀ k : ↥K) : G) * k)⁻¹ = _
      rw [hα₀app]
      have hx1 : (t₀ : G)⁻¹ * (y * (x : G) * y⁻¹) * t₀ ∈ K :=
        SzPair.conj_inv_mem_of_mem_normalizer (hTN ht₀v)
          (SzPair.conj_mem_of_mem_normalizer (hLvN hyLv) x.2)
      have e1 := hky _ x.2
      have e2 := hky _ hx1
      calc (t₀ : G) * k * (t₀ : G)⁻¹ * k * x * ((t₀ : G) * k * (t₀ : G)⁻¹ * k)⁻¹ =
          (t₀ : G) * (k * ((t₀ : G)⁻¹ * (k * x * (k : G)⁻¹) * t₀) * (k : G)⁻¹) * (t₀ : G)⁻¹ := by
            group
        _ = (t₀ : G) * (y * ((t₀ : G)⁻¹ * (y * x * y⁻¹) * t₀) * y⁻¹) * (t₀ : G)⁻¹ := by
            rw [← e1, ← e2]
        _ = (t₀ : G) * y * (t₀ : G)⁻¹ * y * x * ((t₀ : G) * y * (t₀ : G)⁻¹ * y)⁻¹ := by group
    have h2 : (α₀ k * k) ^ 2 ^ j = 1 := by
      apply hconj
      rw [map_pow, hconjw, ← map_pow, map_one]
      have : (⟨_, hwW⟩ : ↥W) ^ 2 ^ j = 1 := Subtype.ext (by simpa using hj)
      rw [this, map_one]
    have hwH : α₀ k * k ∈ H := show MulAut.conj (α₀ k * k) ∈ φ.range from
      hconjw ▸ ⟨⟨_, hwW⟩, rfl⟩
    rw [hP]
    exact ConfSz.mem_of_two_pow hsyl (α₀ k * k).2 ((hNP _).1 (hHN hwH))
      (by simpa using congrArg Subtype.val h2)
  have h5 := hF5 α₀ hα₀P k hkN hkord hinv h (hE₉N hhE) hh3
  have hcomm : α₀ h * h⁻¹ ∈ (P : Subgroup ↥K) := by
    rw [hP]
    have hc1 : (t₀ : G) * h * (t₀ : G)⁻¹ * ((h : ↥K) : G)⁻¹ ∈ K :=
      K.mul_mem (SzPair.conj_mem_of_mem_normalizer (hTN ht₀v) h.2) (K.inv_mem h.2)
    have hc2 : (t₀ : G) * h * (t₀ : G)⁻¹ * ((h : ↥K) : G)⁻¹ ∈
        (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
      have ht₀L : (t₀ : G) ∈ L := (Subgroup.mem_inf.mp ht₀TL).2
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left ?_, ?_⟩
      · have h1 : ((h : ↥K) : G) * (t₀ : G)⁻¹ * ((h : ↥K) : G)⁻¹ ∈ L :=
          SzPair.conj_mem_of_mem_normalizer (S.NV_le_M hhB.1) (L.inv_mem ht₀L)
        rw [show (t₀ : G) * h * (t₀ : G)⁻¹ * ((h : ↥K) : G)⁻¹ =
          (t₀ : G) * (((h : ↥K) : G) * (t₀ : G)⁻¹ * ((h : ↥K) : G)⁻¹) by group]
        exact L.mul_mem ht₀L h1
      · exact Subgroup.mul_mem _
          (SzPair.conj_mem_of_mem_normalizer (ConfSz.mem_normalizer_centralizer t₀.2) hhC)
          (Subgroup.inv_mem _ hhC)
    have hR : K ⊓ ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) ≤ S.Tv ⊓ K := by
      refine ConfSz.le_of_isPGroup hsyl inf_le_left ?_ fun s hs => ?_
      · have h1 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
          rw [S.cLT]
          exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)
        exact h1.to_le inf_le_right
      · obtain ⟨hsTv, hsK⟩ := Subgroup.mem_inf.mp hs
        have hsT : s ∈ T := (Subgroup.mem_inf.mp hsTv).1
        exact ConfSz.mem_normalizer_inf (Subgroup.le_normalizer hsK)
          (ConfSz.mem_normalizer_inf (Subgroup.le_normalizer (Subgroup.mem_sup_right hsT))
            (ConfSz.mem_normalizer_centralizer (S.frame.T_le hsT)))
    have := hR (Subgroup.mem_inf.mpr ⟨hc1, hc2⟩)
    simpa [hα₀app] using this
  have hh2 : h * h ∈ (P : Subgroup ↥K) := by
    have := (P : Subgroup ↥K).mul_mem ((P : Subgroup ↥K).inv_mem hcomm) h5
    simpa [mul_assoc] using this
  have hhP : h ∈ (P : Subgroup ↥K) := by
    have h4 : h = (h * h) * (h * h) := by
      calc h = h ^ 3 * h := by rw [hh3, one_mul]
        _ = (h * h) * (h * h) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [h4]
    exact (P : Subgroup ↥K).mul_mem hh2 hh2
  obtain ⟨m, hm⟩ := P.isPGroup' ⟨h, hhP⟩
  have hm' : h ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hord1 : orderOf h ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
  have hord3 : orderOf h ∣ 3 := orderOf_dvd_of_pow_eq_one hh3
  have hcop : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left m (by norm_num)
  exact hh1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hord1
    hcop) hord3))

end CFSG.Quasithin.H13.A5
