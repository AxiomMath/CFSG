module

public import CFSG.Quasithin.H13.A6S1372L74i
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4V2
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.Quasithin.H13.A6S1372L74a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L74

theorem exists_conj_of_cube {E : Type} [Group E]
    (hE : Nonempty (E ≃* alternatingGroup (Fin 5)) ∨ LieModel E .PSL 3 2 1) {α : MulAut E}
    (hα : α ^ 3 = 1) : ∃ z : E, α = MulAut.conj z := by
  rcases hE with hA | hL
  · obtain ⟨e⟩ := hA
    have hσ : LieType.SteinbergBR.AltFiveGL3.autEquivPerm e α ∈ alternatingGroup (Fin 5) := by
      rw [Perm.mem_alternatingGroup]
      have h1 : Perm.sign (LieType.SteinbergBR.AltFiveGL3.autEquivPerm e α) ^ 3 = 1 := by
        rw [← map_pow, ← map_pow, hα, map_one, map_one]
      rcases Int.units_eq_one_or (Perm.sign (LieType.SteinbergBR.AltFiveGL3.autEquivPerm e α))
        with h | h
      · exact h
      · rw [h] at h1
        exact absurd h1 (by decide)
    refine ⟨e.symm ⟨_, hσ⟩, ?_⟩
    rw [← LieType.SteinbergBR.AltFiveGL3.autEquivPerm_symm_eq_conj e hσ,
      MulEquiv.symm_apply_apply]
  · obtain ⟨e⟩ := LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL
    have hin : MulAut.congr e α ∈ (MulAut.conj : Setup.Family.GL32 →*
        MulAut Setup.Family.GL32).range := by
      have h4 : MulAut.congr e α = (MulAut.congr e α ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, ← map_pow, hα, map_one,
          one_mul]
      rw [h4]
      exact Subgroup.sq_mem_of_index_two LieType.SteinbergBR.AutGL32.index_inner _
    obtain ⟨z, hz⟩ := hin
    refine ⟨e.symm z, (MulAut.congr e).injective ?_⟩
    rw [LieType.SteinbergBR.AltFiveGL3.congr_conj, MulEquiv.apply_symm_apply, hz]

theorem conj_injective_of {E : Type} [Group E]
    (hE : Nonempty (E ≃* alternatingGroup (Fin 5)) ∨ LieModel E .PSL 3 2 1) :
    Function.Injective (MulAut.conj : E →* MulAut E) := by
  intro z w h
  rcases hE with hA | hL
  · obtain ⟨e⟩ := hA
    have hc : ∀ y : E, MulAut.conj y =
        (LieType.SteinbergBR.AltFiveGL3.autEquivPerm e).symm (e y : Perm (Fin 5)) := fun y => by
      rw [LieType.SteinbergBR.AltFiveGL3.autEquivPerm_symm_eq_conj e (e y).2]
      simp
    rw [hc, hc] at h
    exact e.injective (Subtype.ext ((LieType.SteinbergBR.AltFiveGL3.autEquivPerm e).symm.injective
      h))
  · obtain ⟨e⟩ := LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL
    have h1 := congrArg (MulAut.congr e) h
    rw [LieType.SteinbergBR.AltFiveGL3.congr_conj, LieType.SteinbergBR.AltFiveGL3.congr_conj]
      at h1
    exact e.injective (LieType.SteinbergBR.AutGL32.conj_injective h1)

theorem center_eq_bot_of {E : Type} [Group E]
    (hE : Nonempty (E ≃* alternatingGroup (Fin 5)) ∨ LieModel E .PSL 3 2 1) :
    Subgroup.center E = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply conj_injective_of hE
  rw [map_one]
  ext y
  rw [MulAut.conj_apply, ← Subgroup.mem_center_iff.mp hz y, mul_inv_cancel_right,
    MulAut.one_apply]

variable {G : Type} [Group G]

theorem mem_pCoreOf_of_act_eq_one {K : Subgroup G} (hZ : Subgroup.center (ModO2 K) = ⊥) {y : G}
    (hy : y ∈ K) (h1 : actModO2_614 K ⟨y, Subgroup.le_normalizer hy⟩ = 1) :
    y ∈ pCoreOf 2 K := by
  rw [actModO2_614_of_mem] at h1
  have hc : ((⟨y, hy⟩ : ↥K) : ModO2 K) ∈ Subgroup.center (ModO2 K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have := congrArg (fun φ : MulAut (ModO2 K) => φ z) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc
  exact mem_pCoreOf_of_mem_pCore614 hc

variable [Finite G]

theorem exists_cube_act {K : Subgroup G}
    (hE : Nonempty (ModO2 K ≃* alternatingGroup (Fin 5)) ∨ LieModel (ModO2 K) .PSL 3 2 1)
    {x : G} (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx3 : x ^ 3 = 1)
    (hx1 : actModO2_614 K ⟨x, hxN⟩ ≠ 1) :
    ∃ k ∈ K, k ^ 3 = 1 ∧ k ≠ 1 ∧ ∃ m : ℕ, ∀ (hk : k ∈ Subgroup.normalizer (K : Set G))
      (hxm : x ^ m ∈ Subgroup.normalizer (K : Set G)),
      actModO2_614 K ⟨k, hk⟩ = actModO2_614 K ⟨x ^ m, hxm⟩ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hα3 : actModO2_614 K ⟨x, hxN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have e : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx3)
    rw [e, map_one]
  obtain ⟨z, hz⟩ := exists_conj_of_cube hE hα3
  obtain ⟨k₁, rfl⟩ := QuotientGroup.mk_surjective z
  have hk₁ : actModO2_614 K ⟨(k₁ : G), Subgroup.le_normalizer k₁.2⟩ =
      actModO2_614 K ⟨x, hxN⟩ := by
    rw [actModO2_614_of_mem K k₁.2, hz]
  have h3 : 3 ∣ orderOf (k₁ : G) := by
    have h1 := orderOf_map_dvd (actModO2_614 K) ⟨(k₁ : G), Subgroup.le_normalizer k₁.2⟩
    rw [hk₁, orderOf_eq_prime hα3 hx1, Subgroup.orderOf_mk] at h1
    exact h1
  have hn : 0 < orderOf (k₁ : G) := orderOf_pos _
  refine ⟨(k₁ : G) ^ (orderOf (k₁ : G) / 3), K.pow_mem k₁.2 _, ?_, ?_, orderOf (k₁ : G) / 3,
    fun hk hxm => ?_⟩
  · rw [← pow_mul, Nat.div_mul_cancel h3, pow_orderOf_eq_one]
  · exact pow_ne_one_of_lt_orderOf (by omega) (by omega)
  · have e1 : (⟨(k₁ : G) ^ (orderOf (k₁ : G) / 3), hk⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨(k₁ : G), Subgroup.le_normalizer k₁.2⟩ ^ (orderOf (k₁ : G) / 3) := Subtype.ext (by simp)
    have e2 : (⟨x ^ (orderOf (k₁ : G) / 3), hxm⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨x, hxN⟩ ^ (orderOf (k₁ : G) / 3) := Subtype.ext (by simp)
    rw [e1, e2, map_pow, map_pow, hk₁]

theorem mem_normalizer_pCoreOf_of_act {K X T : Subgroup G} (hZ : Subgroup.center (ModO2 K) = ⊥)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hTX : T ≤ X) (hT : quasithinIsSylowTwo T)
    {k x : G} (hk : k ∈ K) (hx : x ∈ X)
    (hkx : actModO2_614 K ⟨k, Subgroup.le_normalizer hk⟩ = actModO2_614 K ⟨x, hXN hx⟩) :
    k ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRX : pCoreOf 2 X ≤ X := pCoreOf_le 2 X
  have hXR : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := le_normalizer_pCoreOf 2 X
  obtain ⟨E, hE⟩ : ∃ E : Subgroup G, E = ((((pCoreOf 2 X).subgroupOf
      (Subgroup.normalizer (K : Set G))).map (actModO2_614 K)).comap (actModO2_614 K)).map
      (Subgroup.normalizer (K : Set G)).subtype ⊓ K := ⟨_, rfl⟩
  have hmem : ∀ y (hy : y ∈ K) r (hr : r ∈ pCoreOf 2 X),
      actModO2_614 K ⟨y, Subgroup.le_normalizer hy⟩ = actModO2_614 K ⟨r, hXN (hRX hr)⟩ →
      y ∈ E := by
    intro y hy r hr h
    rw [hE]
    exact ⟨⟨⟨y, Subgroup.le_normalizer hy⟩, ⟨⟨r, hXN (hRX hr)⟩, hr, h.symm⟩, rfl⟩, hy⟩
  have hmem' : ∀ y ∈ E, ∃ hy : y ∈ K, ∃ r, ∃ hr : r ∈ pCoreOf 2 X,
      actModO2_614 K ⟨y, Subgroup.le_normalizer hy⟩ = actModO2_614 K ⟨r, hXN (hRX hr)⟩ := by
    intro y hy
    rw [hE] at hy
    obtain ⟨⟨⟨y', hy'N⟩, ⟨⟨r, hrN⟩, hr, hρr⟩, rfl⟩, hyK⟩ := hy
    exact ⟨hyK, r, hr, hρr.symm⟩
  have hE2 : IsPGroup 2 E := by
    rintro ⟨y, hy⟩
    obtain ⟨hyK, r, hr, hρ⟩ := hmem' y hy
    obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 X) ⟨r, hr⟩
    have hra : r ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hyaK : y ^ 2 ^ a ∈ K := K.pow_mem hyK _
    have h1 : actModO2_614 K ⟨y ^ 2 ^ a, Subgroup.le_normalizer hyaK⟩ = 1 := by
      have e1 : (⟨y ^ 2 ^ a, Subgroup.le_normalizer hyaK⟩ :
          ↥(Subgroup.normalizer (K : Set G))) = ⟨y, Subgroup.le_normalizer hyK⟩ ^ 2 ^ a :=
        Subtype.ext (by simp)
      have e2 : (⟨r, hXN (hRX hr)⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 ^ a = 1 :=
        Subtype.ext (by simpa using hra)
      rw [e1, map_pow, hρ, ← map_pow, e2, map_one]
    have h2 := mem_pCoreOf_of_act_eq_one hZ hyaK h1
    obtain ⟨b, hb⟩ := (pCoreOf_isPGroup 2 K) ⟨_, h2⟩
    have hyb : (y ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have hy' : y ^ 2 ^ (a + b) = 1 := by rw [pow_add, pow_mul, hyb]
    exact ⟨a + b, Subtype.ext (by simpa using hy')⟩
  have hXE : X ≤ Subgroup.normalizer (E : Set G) := by
    intro g hg
    refine A6L19.mem_normalizer_of_conj fun y hy => ?_
    obtain ⟨hyK, r, hr, hρ⟩ := hmem' y hy
    have hgN := hXN hg
    have hyK' : g * y * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hgN y).mp hyK
    have hr' : g * r * g⁻¹ ∈ pCoreOf 2 X := (Subgroup.mem_normalizer_iff.mp (hXR hg) r).mp hr
    refine hmem _ hyK' _ hr' ?_
    have e1 : (⟨g * y * g⁻¹, Subgroup.le_normalizer hyK'⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨g, hgN⟩ * ⟨y, Subgroup.le_normalizer hyK⟩ * ⟨g, hgN⟩⁻¹ := rfl
    have e2 : (⟨g * r * g⁻¹, hXN (hRX hr')⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨g, hgN⟩ * ⟨r, hXN (hRX hr)⟩ * ⟨g, hgN⟩⁻¹ := rfl
    rw [e1, e2]
    simp only [map_mul, map_inv, hρ]
  obtain ⟨Syl, hSyl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hET : E ≤ T := by
    have hP : IsPGroup 2 (E ⊔ T : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hE2 hT.1 (hTX.trans hXE)
    have hTP : (Syl : Subgroup G) ≤ E ⊔ T := by
      rw [hSyl]
      exact le_sup_right
    have h := Syl.is_maximal' hP hTP
    rw [hSyl] at h
    exact le_sup_left.trans h.le
  have hER : E ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 (hET.trans hTX) hXE hE2
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
  refine A6L19.mem_normalizer_of_conj fun r hr => ?_
  have hrN : r ∈ Subgroup.normalizer (K : Set G) := hXN (hRX hr)
  have hcK : k * r * k⁻¹ * r⁻¹ ∈ K := by
    have h1 : r * k⁻¹ * r⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hrN k⁻¹).mp (K.inv_mem hk)
    have e : k * r * k⁻¹ * r⁻¹ = k * (r * k⁻¹ * r⁻¹) := by group
    rw [e]
    exact K.mul_mem hk h1
  have hxr : x * r * x⁻¹ * r⁻¹ ∈ pCoreOf 2 X :=
    (pCoreOf 2 X).mul_mem ((Subgroup.mem_normalizer_iff.mp (hXR hx) r).mp hr)
      ((pCoreOf 2 X).inv_mem hr)
  have hc : k * r * k⁻¹ * r⁻¹ ∈ E := by
    refine hmem _ hcK _ hxr ?_
    have e1 : (⟨k * r * k⁻¹ * r⁻¹, Subgroup.le_normalizer hcK⟩ :
        ↥(Subgroup.normalizer (K : Set G))) = ⟨k, hkN⟩ * ⟨r, hrN⟩ * ⟨k, hkN⟩⁻¹ * ⟨r, hrN⟩⁻¹ :=
      rfl
    have e2 : (⟨x * r * x⁻¹ * r⁻¹, hXN (hRX hxr)⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨x, hXN hx⟩ * ⟨r, hrN⟩ * ⟨x, hXN hx⟩⁻¹ * ⟨r, hrN⟩⁻¹ := rfl
    rw [e1, e2]
    simp only [map_mul, map_inv, hkx]
  have e : k * r * k⁻¹ = (k * r * k⁻¹ * r⁻¹) * r := by group
  rw [e]
  exact (pCoreOf 2 X).mul_mem (hER hc) hr

end A6L74

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem exists_L1_act_ne_one (hhat : ¬ IsHatA6 L)
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hc : ¬ ∀ k ∈ K, ∀ l ∈ S.L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 K) :
    ∃ x, ∃ hxN : x ∈ Subgroup.normalizer (K : Set G), x ∈ S.L1 ∧ x ^ 3 = 1 ∧
      actModO2_614 K ⟨x, hxN⟩ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1N : S.L1 ≤ Subgroup.normalizer (K : Set G) := (le_sup_left.trans hH.1.1).trans hHK
  by_contra hno
  push Not at hno
  apply hc
  have hle : S.L1 ≤ (actModO2_614 K).ker.map (Subgroup.normalizer (K : Set G)).subtype := by
    show oTwoRes (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) ≤ _
    rw [oTwoRes, Subgroup.closure_le]
    rintro x ⟨hx, m, hm, hxm⟩
    have hxL1 : x ∈ S.L1 := Subgroup.subset_closure ⟨hx, m, hm, hxm⟩
    refine ⟨⟨x, hL1N hxL1⟩, MonoidHom.mem_ker.mpr (hno x (hL1N hxL1) hxL1 ?_), rfl⟩
    obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, S.cube_mem_pCoreOf_L1 hhat hxL1⟩
    have ha' : (x ^ 3) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hm' : (x ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxm, one_pow]
    exact A6L19.eq_one_of_odd_of_two hm hm' ha'
  have hall : ∀ l (hl : l ∈ S.L1), actModO2_614 K ⟨l, hL1N hl⟩ = 1 := by
    intro l hl
    obtain ⟨n, hn, hnl⟩ := hle hl
    have e : n = ⟨l, hL1N hl⟩ := Subtype.ext hnl
    rw [e] at hn
    exact hn
  have hcomm := commutator_le_pCoreOf_of_actModO2_614 hL1N hall
  intro k hk l hl
  have h1 := (pCoreOf 2 K).inv_mem (hcomm (Subgroup.commutator_mem_commutator hl hk))
  rwa [commutatorElement_inv, commutatorElement_def] at h1

end Setting4

theorem lem1374OneDiag_of (h1227 : U3.Stmt13_2_2_7)
    (h1337 : Stmt13_3_7) : Lem1374OneDiag := by
  intro G _ _ T L V S _ _ hhat H hH _ hB K hKc hHK h52 hL1K hc
  have hKH : K ≤ H := le_of_mem_cComp hKc
  obtain ⟨x, hxN, hxL, hx3, hx1⟩ := Setting4.exists_L1_act_ne_one hhat hH hHK hc
  obtain ⟨k, hkK, hk3, hk1, m, hkm⟩ := A6L74.exists_cube_act h52 hxN hx3 hx1
  have hXN : S.L1 ⊔ T ≤ Subgroup.normalizer (K : Set G) := hH.1.1.trans hHK
  have hxm : x ^ m ∈ S.L1 ⊔ T := (S.L1 ⊔ T).pow_mem (Subgroup.mem_sup_left hxL) m
  have hkR := A6L74.mem_normalizer_pCoreOf_of_act (A6L74.center_eq_bot_of h52) hXN le_sup_right
    S.h13.sylow hkK hxm (hkm _ _)
  have hRM : Subgroup.normalizer (pCoreOf 2 (S.L1 ⊔ T) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
    rcases h1227 G T L V S.L1 S.h13 S.irr S.zv (fun h => absurd h hhat) (fun _ => rfl) S.a6
      with h | h
    · exact S.normalizer_R1_le_M h
    · exact absurd h hB
  exact hk1 (Setting4.eq_one_of_cube_of_mem_M hH h1337 hhat hKH hHK hL1K hkK hk3 (hRM hkR))

end CFSG.Quasithin.H13.A6
