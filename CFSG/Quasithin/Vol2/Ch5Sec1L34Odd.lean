module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs517
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

section General

variable {G : Type} [Group G]

theorem conj_mem_centralizerModO2 {X : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hc : c ∈ centralizerModO2 X) :
    g * c * g⁻¹ ∈ centralizerModO2 X := by
  obtain ⟨hcN, hcO, hcu⟩ := hc
  have hgO : g ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 X hg
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hcN) (Subgroup.inv_mem _ hg),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgO hcO) (Subgroup.inv_mem _ hgO), fun u hu => ?_⟩
  have hu' : g⁻¹ * u * g ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) u).mp hu
    simpa using this
  have h2 := (Subgroup.mem_normalizer_iff.mp hgO _).mp (hcu _ hu')
  have e : g * (c * (g⁻¹ * u * g) * c⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ =
      g * c * g⁻¹ * u * (g * c * g⁻¹)⁻¹ * u⁻¹ := by group
  rw [← e]
  exact h2

theorem center_eq_bot_of_isSimpleGroup_of_four_dvd {X : Type} [Group X] [IsSimpleGroup X]
    [Finite X] (h4 : 4 ∣ Nat.card X) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hc : ∀ a b : X, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hc }
    have hp : (Nat.card X).Prime := IsSimpleGroup.prime_card
    have h2 : 2 ∣ Nat.card X := (show 2 ∣ 4 by norm_num).trans h4
    have h2eq : Nat.card X = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
    rw [h2eq] at h4
    norm_num at h4

end General

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_0_1

variable (h : Hyp5_0_1 G T M L n)
include h

theorem center_O2Q_eq_bot : Subgroup.center (O2Q L) = ⊥ := by
  have := h.isSimple
  refine center_eq_bot_of_isSimpleGroup_of_four_dvd ?_
  rw [card_of_lieModel_L2 (by have := h.two_le; omega) h.lie]
  refine Dvd.dvd.mul_right ?_ _
  obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by have := h.two_le; omega⟩
  rw [hk, pow_add]
  exact Dvd.intro_left _ rfl

theorem inf_centralizerModO2_le_pCoreOf :
    (L ⊔ T) ⊓ centralizerModO2 L ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLT := h.sup_le_normalizer
  have hZ := h.center_O2Q_eq_bot
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun g hg => ?_) ?_
  · refine mem_normalizer_of_forall_conj_mem' fun c hc => ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hc.1) (Subgroup.inv_mem _ hg)
    · exact conj_mem_centralizerModO2 (hLT hg) hc.2
  · rintro ⟨c, hc1, hc2⟩
    have hcLT : c ∈ ((L ⊔ T : Subgroup G) : Set G) := hc1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L T h.T_le_normalizer] at hcLT
    obtain ⟨l, hl, t, ht, rfl⟩ := hcLT
    obtain ⟨k, hk⟩ := h.sylow.1 ⟨t, ht⟩
    have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨l', hl', he⟩ := pow_mul_mem_of_mem_normalizer hl (h.T_le_normalizer ht) (2 ^ k)
    rw [htk, mul_one] at he
    have hcC : (l * t) ^ 2 ^ k ∈ centralizerModO2 L := Subgroup.pow_mem _ hc2 _
    rw [he] at hcC
    have hO := mem_pCoreOf_of_mem_centralizerModO2 hZ hl' hcC
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 L ⟨l', hO⟩
    have hj' : l' ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    refine ⟨k + j, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, he, hj']

theorem exists_inv_mul_mem_of_odd (hI : L2OddInnerFact) (hn : Odd n) {t : G} (ht : t ∈ T) :
    ∃ l ∈ L, l⁻¹ * t ∈ pCoreOf 2 (L ⊔ T) := by
  have htN : t ∈ Subgroup.normalizer (L : Set G) := h.T_le_normalizer ht
  obtain ⟨k, hk⟩ := h.sylow.1 ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hφ : quotConjAut L ⟨t, htN⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨t, htN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using htk)
    rw [this, map_one]
  obtain ⟨x, hx⟩ := hI (O2Q L) n h.lie hn _ ⟨k, hφ⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  have hlN : (l : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer l.2
  have hl : quotConjAut L ⟨l, hlN⟩ = MulAut.conj (QuotientGroup.mk l : O2Q L) := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H u =>
      rw [quotConjAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul]
      congr 1
  refine ⟨l, l.2, h.inf_centralizerModO2_le_pCoreOf ⟨?_, ?_⟩⟩
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (L.inv_mem l.2)) (Subgroup.mem_sup_right ht)
  · have hyN : (l : G)⁻¹ * t ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hlN) htN
    have hy : quotConjAut L ⟨(l : G)⁻¹ * t, hyN⟩ = 1 := by
      have e : (⟨(l : G)⁻¹ * t, hyN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          (⟨l, hlN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ * ⟨t, htN⟩ := rfl
      rw [e, map_mul, map_inv, hl, hx, inv_mul_cancel]
    refine ⟨hyN, normalizer_le_normalizer_pCoreOf 2 L hyN, fun u hu => ?_⟩
    exact commutator_mem_of_quotConjAut_eq_one hy ⟨u, hu⟩

theorem exists_eq_mul_of_odd (hI : L2OddInnerFact) (hn : Odd n) {t : G} (ht : t ∈ T) :
    ∃ l ∈ T ⊓ L, ∃ q ∈ pCoreOf 2 (L ⊔ T), t = l * q := by
  obtain ⟨l, hl, hq⟩ := h.exists_inv_mul_mem_of_odd hI hn ht
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_le_of_isSylowTwoOf (h.isSylowTwoOf le_sup_right)
  refine ⟨l, ⟨?_, hl⟩, _, hq, by group⟩
  have : (l : G) = t * (l⁻¹ * t)⁻¹ := by group
  rw [this]
  exact T.mul_mem ht (T.inv_mem (hQT hq))

theorem borelL_le_normalizer_T_of_odd (hI : L2OddInnerFact) (hn : Odd n) :
    borelL T L ≤ Subgroup.normalizer (T : Set G) := by
  intro d hd
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_le_of_isSylowTwoOf (h.isSylowTwoOf le_sup_right)
  refine mem_normalizer_of_forall_conj_mem' fun t ht => ?_
  obtain ⟨l, hl, q, hq, rfl⟩ := h.exists_eq_mul_of_odd hI hn ht
  have h1 : d * l * d⁻¹ ∈ T ⊓ L := (Subgroup.mem_normalizer_iff.mp hd.2 l).mp hl
  have h2 : d * q * d⁻¹ ∈ pCoreOf 2 (L ⊔ T) :=
    (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hd.1)) q).mp hq
  have e : d * (l * q) * d⁻¹ = (d * l * d⁻¹) * (d * q * d⁻¹) := by group
  rw [e]
  exact T.mul_mem h1.1 (hQT h2)

end Hyp5_0_1

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem D_le_normalizer_K_of_odd (h515 : Stmt5_1_15) (hn : Odd n) :
    D ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  rcases h515 G T M L V H B D n h.hyp h.notation59 h.module h.l34 with
    hD | ⟨h2, -⟩ | ⟨h24, -⟩ | ⟨h48, -⟩
  · exact hD
  all_goals exfalso
  · subst h2; exact absurd hn (by decide)
  · rcases h24 with rfl | rfl <;> exact absurd hn (by decide)
  · rcases h48 with rfl | rfl <;> exact absurd hn (by decide)

theorem coprime_card_D_of_odd (hF : L2TorusFact) (hn : Odd n) : Nat.Coprime (Nat.card D) 6 := by
  rw [(h.hyp.toHyp5_0_1.isCyclic_card_of_isHall hF h.notation59.2.1).2]
  obtain ⟨k, rfl⟩ := hn
  have h4 : (2 : ℕ) ^ (2 * k + 1) = 2 * 4 ^ k := by rw [pow_succ, pow_mul]; ring
  rw [h4]
  have hpos : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have hmod : (2 * 4 ^ k - 1) % 6 = 1 ∨ (2 * 4 ^ k - 1) % 6 = 5 := by
    have h3 : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]; norm_num
    omega
  have hodd : Odd (2 * 4 ^ k - 1) := Nat.odd_iff.mpr (by omega)
  have h3 : ¬ 3 ∣ 2 * 4 ^ k - 1 := by omega
  rw [show (6 : ℕ) = 2 * 3 by norm_num]
  exact Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hodd)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm

theorem D_le_centralizerModO2_of_odd (hI : L2OddInnerFact) (hL : L34SylowNormFact)
    (hF : L2TorusFact) (h515 : Stmt5_1_15) (hn : Odd n) :
    D ≤ centralizerModO2 (oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  set K := oTwoUpper H with hKdef
  have hDK := h.D_le_normalizer_K_of_odd h515 hn
  have hDT : D ≤ Subgroup.normalizer (T : Set G) :=
    h.notation59.2.1.1.trans (hh.borelL_le_normalizer_T_of_odd hI hn)
  have hTH : T ≤ H := h.hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf hTH) (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  set π : ↥K →* O2Q K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hS := isSylowTwoOf_map_hom' hTK π
  rw [MonoidHom.range_eq_top_of_surjective π hπs] at hS
  set S := ((T ⊓ K).subgroupOf K).map π with hSdef
  have hcop := h.coprime_card_D_of_odd hF hn
  intro d hd
  have hdK : d ∈ Subgroup.normalizer (K : Set G) := hDK hd
  set φ := quotConjAut K ⟨d, hdK⟩ with hφ
  have hφS : S.map φ.toMonoidHom = S := by
    have hdT : d ∈ Subgroup.normalizer (T : Set G) := hDT hd
    have hle : S.map φ.toMonoidHom ≤ S := by
      rintro _ ⟨_, ⟨x, hx', rfl⟩, rfl⟩
      have hx : (x : G) ∈ T ⊓ K := hx'
      have hxK : d * (x : G) * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hdK x).mp x.2
      refine ⟨⟨d * x * d⁻¹, hxK⟩, ?_, ?_⟩
      · show d * (x : G) * d⁻¹ ∈ T ⊓ K
        exact ⟨(Subgroup.mem_normalizer_iff.mp hdT x).mp hx.1, hxK⟩
      · show π ⟨d * x * d⁻¹, hxK⟩ = quotConjAut K ⟨d, hdK⟩ (π x)
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, quotConjAut_mk]
    have hinj : Function.Injective φ.toMonoidHom := φ.injective
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective hinj])
  have hord : Nat.Coprime (orderOf φ) 6 := by
    have h1 : orderOf φ ∣ orderOf (⟨d, hd⟩ : ↥D) := by
      apply orderOf_dvd_of_pow_eq_one
      have : (⟨d, hdK⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ orderOf (⟨d, hd⟩ : ↥D) = 1 := by
        apply Subtype.ext
        have := pow_orderOf_eq_one (⟨d, hd⟩ : ↥D)
        simp
      rw [hφ, ← map_pow, this, map_one]
    exact Nat.Coprime.coprime_dvd_left (h1.trans (orderOf_dvd_natCard _)) hcop
  have hφ1 := hL (O2Q K) h.l34 S hS φ hφS hord
  refine ⟨hdK, normalizer_le_normalizer_pCoreOf 2 K hdK, fun u hu => ?_⟩
  exact commutator_mem_of_quotConjAut_eq_one hφ1 ⟨u, hu⟩

end Hyp5_1_14

end CFSG.Quasithin.H13
