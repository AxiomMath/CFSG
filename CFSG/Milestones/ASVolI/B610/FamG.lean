module

public import CFSG.Milestones.ASVolI.B610.FamF
public import CFSG.Milestones.ASVolI.B610.Frat
public import CFSG.Quasithin.EmptyFaithful.LRed10Core
public import CFSG.Milestones.ASVolI.B610.FamE
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] noncomputable def burnsideB610_centStar {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (Y : Subgroup G) : Subgroup G :=
  ((Subgroup.centralizer ((autI hV Y : Subgroup (MulAut (IntMod V hV))) :
    Set (MulAut (IntMod V hV)))).comap (convI hV)).map (Subgroup.normalizer (V : Set G)).subtype

theorem burnsideB610_mem_centStar {V : Subgroup G} {hV : IsElemAbelian 2 V} {Y : Subgroup G}
    {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hc : convI hV ⟨g, hg⟩ ∈ Subgroup.centralizer ((autI hV Y : Subgroup (MulAut (IntMod V hV))) :
      Set (MulAut (IntMod V hV)))) : g ∈ burnsideB610_centStar hV Y :=
  ⟨⟨g, hg⟩, hc, rfl⟩

theorem burnsideB610_autI_cjSub_of_mem_centStar {V : Subgroup G} {hV : IsElemAbelian 2 V}
    {Y Z : Subgroup G} (hZY : Z ≤ Y) {g : G} (hg : g ∈ burnsideB610_centStar hV Y) :
    autI hV (cjSub g Z) = autI hV Z := by
  obtain ⟨⟨g, hgN⟩, hgc, rfl⟩ := hg
  show autI hV (cjSub g Z) = autI hV Z
  rw [← autI_cjSub hV hgN Z]
  ext ψ
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    have hφY : φ ∈ autI hV Y := autI_mono hV hZY hφ
    have hcomm := Subgroup.mem_centralizer_iff.mp hgc φ hφY
    show convI hV ⟨g, hgN⟩ * φ * (convI hV ⟨g, hgN⟩)⁻¹ ∈ autI hV Z
    rw [← hcomm, mul_inv_cancel_right]
    exact hφ
  · intro hψ
    have hψY : ψ ∈ autI hV Y := autI_mono hV hZY hψ
    have hcomm := Subgroup.mem_centralizer_iff.mp hgc ψ hψY
    refine ⟨ψ, hψ, ?_⟩
    show convI hV ⟨g, hgN⟩ * ψ * (convI hV ⟨g, hgN⟩)⁻¹ = ψ
    rw [← hcomm, mul_inv_cancel_right]

namespace burnsideB610_Fam

variable {H T V : Subgroup G} {hV : IsElemAbelian 2 V} {F : Type} [Field F] {ι : Type}
  {S : Finset ι} {X : ι → Subgroup G} {D : ∀ i, NatData (X i) V F}

theorem le_centStar (hFam : burnsideB610_Fam H T V hV F S X D)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) {i j : ι} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j) : X j ≤ burnsideB610_centStar hV (X i) := by
  intro x hx
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := hHV (hFam.le j hj hx)
  refine burnsideB610_mem_centStar hxN (Subgroup.mem_centralizer_iff.mpr fun φ hφ => ?_)
  obtain ⟨y, hyX, rfl⟩ := (mem_autI hV).1 hφ
  have h1 := hFam.comm i hi j hj hij y hyX x hx
  have h2 : convI hV (y * ⟨x, hxN⟩ * y⁻¹ * (⟨x, hxN⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹) =
      1 := (convI_eq_one_iff hV _).2 (by simpa using h1)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
  calc convI hV y * convI hV ⟨x, hxN⟩
      = (convI hV y * convI hV ⟨x, hxN⟩ * (convI hV y)⁻¹ * (convI hV ⟨x, hxN⟩)⁻¹) *
          (convI hV ⟨x, hxN⟩ * convI hV y) := by group
    _ = convI hV ⟨x, hxN⟩ * convI hV y := by rw [h2, one_mul]

theorem exists_gen [DecidableEq ι] (hFam : burnsideB610_Fam H T V hV F S X D)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) (Bf : ι → Subgroup G)
    (hBX : ∀ i ∈ S, Bf i ≤ X i) (k : ι → G)
    (hk : ∀ i ∈ S, k i ∈ X i ⊓ twoResidual H ∧
      autI hV (X i) ≤ autI hV (Bf i) ⊔ autI hV (cjSub (k i) (Bf i))) :
    ∀ 𝒮 : Finset ι, 𝒮 ⊆ S → ∃ g ∈ ⨆ i ∈ 𝒮, (X i ⊓ twoResidual H),
      ∀ i ∈ 𝒮, autI hV (X i) ≤ autI hV (Bf i) ⊔ autI hV (cjSub g (Bf i)) := by
  intro 𝒮
  induction 𝒮 using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, Subgroup.one_mem _, fun i hi => (Finset.notMem_empty i hi).elim⟩
  | insert Y 𝒮' hY ih =>
    intro hsub
    have hYS : Y ∈ S := hsub (Finset.mem_insert_self Y 𝒮')
    have h𝒮' : 𝒮' ⊆ S := fun i hi => hsub (Finset.mem_insert_of_mem hi)
    obtain ⟨g', hg', hg'X⟩ := ih h𝒮'
    obtain ⟨hkY, hgenY⟩ := hk Y hYS
    refine ⟨g' * k Y, ?_, fun i hi => ?_⟩
    · rw [Finset.iSup_insert]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hg') (Subgroup.mem_sup_left hkY)
    · rw [← burnsideB610_cjSub_cjSub]
      have hXVi : ∀ j ∈ S, X j ≤ Subgroup.normalizer (V : Set G) := fun j hj =>
        (hFam.le j hj).trans hHV
      rcases Finset.mem_insert.mp hi with rfl | hi'
      ·
        have hg'C : g' ∈ burnsideB610_centStar hV (X i) := by
          refine (iSup₂_le fun j hj => ?_ : (⨆ j ∈ 𝒮', (X j ⊓ twoResidual H)) ≤ _) hg'
          have hij : i ≠ j := fun h => hY (h ▸ hj)
          exact inf_le_left.trans (hFam.le_centStar hHV hYS (h𝒮' hj) hij)
        have hle : cjSub (k i) (Bf i) ≤ X i :=
          cjSub_le (Subgroup.le_normalizer hkY.1) (hBX i hYS)
        rw [burnsideB610_autI_cjSub_of_mem_centStar hle hg'C]
        exact hgenY
      · have hiY : Y ≠ i := fun h => hY (h ▸ hi')
        have hkC : k Y ∈ burnsideB610_centStar hV (X i) :=
          hFam.le_centStar hHV (h𝒮' hi') hYS (Ne.symm hiY) hkY.1
        have hg'N : g' ∈ Subgroup.normalizer (V : Set G) := by
          refine (iSup₂_le fun j hj => ?_ : (⨆ j ∈ 𝒮', (X j ⊓ twoResidual H)) ≤ _) hg'
          exact inf_le_left.trans (hXVi j (h𝒮' hj))
        have hBV : cjSub (k Y) (Bf i) ≤ Subgroup.normalizer (V : Set G) :=
          cjSub_le (Subgroup.le_normalizer (hXVi Y hYS hkY.1)) ((hBX i (h𝒮' hi')).trans
            (hXVi i (h𝒮' hi')))
        rw [← autI_cjSub hV hg'N, burnsideB610_autI_cjSub_of_mem_centStar (hBX i (h𝒮' hi')) hkC,
          autI_cjSub hV hg'N]
        exact hg'X i hi'

theorem cardEq [Finite G] [Fintype F] [CharP F 2] [DecidableEq ι] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hFam : burnsideB610_Fam H T V hV F S X D)
    (hred : IsTwoReducedIn H V) (hT : IsSylowTwoOf T H) : LRed10.CardEq V T := by
  intro A hA hAV
  obtain ⟨hc, -, -, -⟩ := hFam.chain hn hF hred hT hA hAV
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans (hT.1.trans hHV)
  have hsq : ∀ v : IntMod V hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have e := B1.card_eq_index_mul (autI hV A)
  rw [B1.index_eq_two_pow hsq, card_fixV_autI hV hAN, hc] at e
  have hA2 : IsPGroup 2 (autI hV A) :=
    (isElemAbelian2_autI hV hA.2.1 hAN).isPGroup
  rw [← card_eq_two_pow_of_isPGroup hA2, card_autI_eq hV hAN] at e
  exact e

theorem two_mul_rkIdx_le [Finite G] [Fintype F] [CharP F 2] [DecidableEq ι] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hFam : burnsideB610_Fam H T V hV F S X D)
    (hred : IsTwoReducedIn H V) (Bf : ι → Subgroup G)
    (hBr : ∀ i ∈ S, rk ↥V ≤ rk ↥(V ⊓ Subgroup.centralizer (Bf i : Set G)) + n)
    (hJ : thompsonJ T ≤ (⨆ i ∈ S, Bf i) ⊔ (H ⊓ Subgroup.centralizer (V : Set G)))
    (hJH : thompsonJ T ≤ H) :
    2 * rkIdx (fixV (autI hV (thompsonJ T))) ≤ rkIdx (fixV (autI hV (twoResidual H))) := by
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hJN : thompsonJ T ≤ Subgroup.normalizer (V : Set G) := hJH.trans hHV
  have hKN : twoResidual H ≤ Subgroup.normalizer (V : Set G) := (twoResidual_le H).trans hHV
  have hJfix := B2F.rkIdx_fixV_autI hV hJN
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => B2F.isElemAbelian_comm hV ha hb
  have hsub := burnsideB610_rk_le_sum hVc (fun i => Subgroup.centralizer (Bf i : Set G)) S
  have hle : V ⊓ ⨅ i ∈ S, Subgroup.centralizer (Bf i : Set G) ≤
      V ⊓ Subgroup.centralizer (thompsonJ T : Set G) := by
    rintro w ⟨hwV, hw⟩
    refine ⟨hwV, ?_⟩
    show w ∈ Subgroup.centralizer (thompsonJ T : Set G)
    have hle' : (⨆ i ∈ S, Bf i) ⊔ (H ⊓ Subgroup.centralizer (V : Set G)) ≤
        Subgroup.centralizer ({w} : Set G) := by
      refine sup_le (iSup₂_le fun i hi b hb => ?_) (fun c hc => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_iInf.mp
          (Subgroup.mem_iInf.mp hw i) hi) b hb).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_iff.mp hc.2 _ hwV
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (Subgroup.mem_centralizer_iff.mp (hle' (hJ hj)) w rfl).symm
  have hr1 := rk_mono hle
  have hsumle : ∑ i ∈ S, (rk ↥V - rk ↥(V ⊓ Subgroup.centralizer (Bf i : Set G))) ≤ S.card * n := by
    have := Finset.sum_le_sum (s := S) (f := fun i =>
      rk ↥V - rk ↥(V ⊓ Subgroup.centralizer (Bf i : Set G))) (g := fun _ => n)
      fun i hi => by have := hBr i hi; omega
    simpa using this
  have hKX : ∀ i ∈ S, twoResidual H ≤ Subgroup.normalizer ((X i : Subgroup G) : Set G) :=
    fun i hi k hk => (hFam.twoResidual_le_nLV hHV hi hk).1
  have hcount := hFam.sum_rkIdx_le hHV hKN hKX S subset_rfl
  have hfix : ∀ i ∈ S, rkIdx (fixV ((D i).img (twoResidual H))) = 2 * n := by
    intro i hi
    rw [hFam.fix i hi]
    have h1 := rk_add_rkIdx (⊥ : Subgroup (CFSG.Quasithin.H.StdMod (Fin 2) F))
    rw [burnsideB610_rk_stdMod hF] at h1
    have h2 : rk ↥(⊥ : Subgroup (CFSG.Quasithin.H.StdMod (Fin 2) F)) = 0 := rk_bot
    omega
  have hsumfix : ∑ i ∈ S, rkIdx (fixV ((D i).img (twoResidual H))) = S.card * (2 * n) := by
    rw [Finset.sum_congr rfl hfix]
    simp
  have hWdef : burnsideB610_famW S X V = ⨆ i ∈ S, (⁅V, X i⁆ : Subgroup G) := rfl
  rw [← hWdef] at hcount
  have hWV := hFam.famW_le hHV
  have hcV : ∀ a ∈ burnsideB610_famW S X V,
      ∀ b ∈ V ⊓ Subgroup.centralizer (twoResidual H : Set G), a * b = b * a :=
    fun a ha b hb => B2F.isElemAbelian_comm hV (hWV ha) hb.1
  have hw1 := B2F.rk_sup_add_rk_inf_of_commute hcV
  have hw2 : burnsideB610_famW S X V ⊓ (V ⊓ Subgroup.centralizer (twoResidual H : Set G)) =
      burnsideB610_famW S X V ⊓ Subgroup.centralizer (twoResidual H : Set G) := by
    rw [← inf_assoc, inf_eq_left.mpr hWV]
  have hw3 : rk ↥(burnsideB610_famW S X V ⊔
      (V ⊓ Subgroup.centralizer (twoResidual H : Set G))) ≤ rk ↥V :=
    rk_mono (sup_le hWV inf_le_left)
  rw [hw2] at hw1
  have hKfix := B2F.rkIdx_fixV_autI hV hKN
  have : S.card * (2 * n) = 2 * (S.card * n) := by ring
  omega

theorem exists_generating [Finite G] [Fintype F] [CharP F 2] [DecidableEq ι] {M : Subgroup G}
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hFam : burnsideB610_Fam H T V hV F S X D)
    (hMP : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (Bf : ι → Subgroup G)
    (hBf : ∀ i ∈ S, Bf i ≤ thompsonJ T ∧ Bf i ≤ X i ∧
      (∀ j ∈ S, j ≠ i → Bf i ≤ Subgroup.centralizer ((⁅V, X j⁆ : Subgroup G) : Set G)) ∧
      Nat.card ((D i).img (Bf i)) = 2 ^ n ∧
      rk ↥V ≤ rk ↥(V ⊓ Subgroup.centralizer (Bf i : Set G)) + n) :
    ∃ g ∈ twoResidual H, g ∈ Subgroup.normalizer (V : Set G) ∧
      twoResidual H ≤ thompsonJ T ⊔ cjSub g (thompsonJ T) := by
  have hT := hMP.isSylow
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hKH : twoResidual H ≤ H := twoResidual_le H
  have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
  have hJH : thompsonJ T ≤ H := hJT.trans hT.1
  have hHC : ¬ H ≤ Subgroup.centralizer (V : Set G) := fun h => hJ (hJH.trans h)
  have hkex : ∀ i : ι, ∃ k : G, i ∈ S → (k ∈ X i ⊓ twoResidual H ∧
      autI hV (X i) ≤ autI hV (Bf i) ⊔ autI hV (cjSub k (Bf i))) := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨hBJ, hBX, -, hBq, -⟩ := hBf i hi
      obtain ⟨k, hk, hgen⟩ := hFam.gen i hi (Bf i) hBX (hT.2.1.to_le (hBJ.trans hJT))
        (by rw [hBq, hF])
      exact ⟨k, fun _ => ⟨hk, hgen⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose k hk using hkex
  obtain ⟨g, hg, hgX⟩ := hFam.exists_gen hHV Bf (fun i hi => (hBf i hi).2.1) k hk S subset_rfl
  have hgK : g ∈ twoResidual H :=
    (iSup₂_le fun i _ => inf_le_right : (⨆ i ∈ S, (X i ⊓ twoResidual H)) ≤ twoResidual H) hg
  have hgN : g ∈ Subgroup.normalizer (V : Set G) := hHV (hKH hgK)
  set I₀ := thompsonJ T ⊔ cjSub g (thompsonJ T) with hI₀
  have hcjH : cjSub g (thompsonJ T) ≤ H := cjSub_le (Subgroup.le_normalizer (hKH hgK)) hJH
  have hI₀H : I₀ ≤ H := sup_le hJH hcjH
  have hI₀N : I₀ ≤ Subgroup.normalizer (V : Set G) := hI₀H.trans hHV
  have hXI : ∀ i ∈ S, X i ≤ I₀ ⊔ (H ⊓ Subgroup.centralizer (V : Set G)) := by
    intro i hi x hx
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := hHV (hFam.le i hi hx)
    have hle : autI hV (Bf i) ⊔ autI hV (cjSub g (Bf i)) ≤ autI hV I₀ :=
      sup_le (autI_mono hV ((hBf i hi).1.trans le_sup_left))
        (autI_mono hV ((cjSub_mono (hBf i hi).1).trans le_sup_right))
    obtain ⟨y, hyI, hyx⟩ := (mem_autI hV).1 (hle (hgX i hi (convI_mem_autI hV hx hxN)))
    have hc : (y : G)⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
      have h1 : convI hV (y⁻¹ * ⟨x, hxN⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
      have := (convI_eq_one_iff hV _).1 h1
      simpa using this
    have hyH : (y : G) ∈ H := hI₀H hyI
    have e : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyI)
      (Subgroup.mem_sup_right ⟨H.mul_mem (H.inv_mem hyH) (hFam.le i hi hx), hc⟩)
  have hKIJ : twoResidual H ≤ I₀ ⊔ kerIn M H := by
    refine hFam.res.trans (iSup₂_le fun i hi => (hXI i hi).trans (sup_le_sup_left ?_ _))
    exact hMP.inf_centralizer_le_kerIn hred hHC
  have hKIQ := burnsideB610_twoResidual_le_sup_pCoreOf hMP hI₀H hKIJ
  have hI₀Q : I₀ ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hI₀H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hcl : conjClosure (thompsonJ T) H ≤ I₀ := by
    refine conjClosure_le fun y hy z hz => ?_
    have hHeq : H = twoResidual H ⊔ T := by rw [sup_comm]; exact (sup_twoResidual_eq hT).symm
    have hTK : T ≤ Subgroup.normalizer (twoResidual H : Set G) :=
      hT.1.trans (le_normalizer_twoResidual H)
    have hy' : y ∈ ((twoResidual H ⊔ T : Subgroup G) : Set G) := by rw [← hHeq]; exact hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTK] at hy'
    obtain ⟨k', hk', t, ht, rfl⟩ := hy'
    have hk'' : k' ∈ ((I₀ ⊔ pCoreOf 2 H : Subgroup G) : Set G) := hKIQ hk'
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hI₀Q] at hk''
    obtain ⟨i, hi, q, hq, rfl⟩ := hk''
    have hqT : q ∈ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT hq
    have hJTN : T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
    have hz' : (q * t) * z * (q * t)⁻¹ ∈ thompsonJ T :=
      (Subgroup.mem_normalizer_iff.mp (hJTN (T.mul_mem hqT ht)) z).mp hz
    have e : i * q * t * z * (i * q * t)⁻¹ = i * ((q * t) * z * (q * t)⁻¹) * i⁻¹ := by group
    rw [e]
    exact I₀.mul_mem (I₀.mul_mem hi (Subgroup.mem_sup_left hz')) (I₀.inv_mem hi)
  have hclJ : ¬ conjClosure (thompsonJ T) H ≤ kerIn M H := by
    intro hle
    apply hJ
    have h1 : thompsonJ T ≤ pCoreOf 2 H :=
      hMP.le_pCoreOf_of_isPGroup_of_le_kerIn (hT.2.1.to_le hJT)
        ((le_conjClosure _ _).trans hle)
    exact h1.trans (MinParabolic.pCoreOf_le_centralizer hred)
  have hclH : conjClosure (thompsonJ T) H ≤ H :=
    conjClosure_le fun y hy z hz => H.mul_mem (H.mul_mem hy (hJH hz)) (H.inv_mem hy)
  have hKcl := (hMP.le_kerIn_or_twoResidual_le hclH (le_normalizer_conjClosure _ _)).resolve_left
    hclJ
  exact ⟨g, hgK, hgN, hKcl.trans hcl⟩

theorem main [Finite G] [Fintype F] [CharP F 2] [DecidableEq ι] {M : Subgroup G} {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (hFam : burnsideB610_Fam H T V hV F S X D)
    (hMP : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    omegaOneCenterOf (thompsonJ T) = (V ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
        (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (twoResidual H : Set G)) ∧
      (∀ i ∈ S, baum T ≤ Subgroup.normalizer ((X i : Subgroup G) : Set G)) ∧
      (∀ i ∈ S, ∃ B : Subgroup G, B ≤ thompsonJ T ∧ B ≤ X i ∧ Nat.card (autI hV B) = 2 ^ n) ∧
      (∀ i ∈ S, V ⊓ Subgroup.centralizer (thompsonJ T : Set G) ≤
        ((⁅V, X i⁆ : Subgroup G) ⊓ Subgroup.centralizer (thompsonJ T : Set G)) ⊔
          (V ⊓ Subgroup.centralizer (thompsonJ T : Set G) ⊓
            Subgroup.centralizer ((X i : Subgroup G) : Set G))) := by
  have hT := hMP.isSylow
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
  have hJH : thompsonJ T ≤ H := hJT.trans hT.1
  obtain ⟨Bf, hBf⟩ := hFam.exists_pieces hn hF hMP hred hJ
  have hJle := hFam.thompsonJ_le_pieces hn hF hred hT Bf
    (fun i hi => ⟨(hBf i hi).1, (hBf i hi).2.1, (hBf i hi).2.2.1, (hBf i hi).2.2.2.1⟩)
  have hBc : ∀ i ∈ S, ∀ j ∈ S, j ≠ i →
      Bf i ≤ Subgroup.centralizer ((⁅V, X j⁆ : Subgroup G) : Set G) :=
    fun i hi => (hBf i hi).2.2.1
  have hBr : ∀ i ∈ S, rk ↥V ≤ rk ↥(V ⊓ Subgroup.centralizer (Bf i : Set G)) + n :=
    fun i hi => (hBf i hi).2.2.2.2
  refine ⟨?_, fun i hi => hFam.baum_le_normalizer hn hF hred hT Bf hBc hBr hJle hi,
    fun i hi => ?_, fun i hi => hFam.le_sup_centralizer hF hred hT Bf hBf hJle hi⟩
  · exact LRed10.baumann_core hV hMP hred hJ (hFam.cardEq hn hF hred hT)
      (hFam.exists_generating hF hMP hred hJ Bf hBf)
      (hFam.two_mul_rkIdx_le hF hred Bf hBr hJle hJH)
  · obtain ⟨hBJ, hBX, -, hBq, -⟩ := hBf i hi
    refine ⟨Bf i, hBJ, hBX, ?_⟩
    have hBV : Bf i ≤ Subgroup.normalizer (V : Set G) := hBX.trans ((hFam.le i hi).trans hHV)
    have hBnLV : Bf i ≤ nLV (X i) V := fun x hx =>
      ⟨hFam.le_normalizer hi hi (hBX hx), hBV hx⟩
    have e1 := burnsideB610_rk_img (D i) (hFam.ker i hi) hBnLV
    have e2 : Bf i ⊓ Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G) =
        Bf i ⊓ Subgroup.centralizer (V : Set G) := by
      apply le_antisymm
      · rintro x ⟨hxB, hxi⟩
        refine ⟨hxB, hFam.faith hred (hFam.le i hi (hBX hxB)) fun j hj => ?_⟩
        by_cases hji : j = i
        · subst hji
          exact hxi
        · exact hBc i hi j hj hji hxB
      · exact inf_le_inf_left _ (Subgroup.centralizer_le (hFam.commutator_le hHV hi))
    rw [e2] at e1
    have e3 := (burnsideB610_rk_of_card_eq_mul (card_autI_mul_card_inf hV hBV).symm).symm
    have hB2 : IsPGroup 2 (autI hV (Bf i)) :=
      B2F.isPGroup_autI hV (hT.2.1.to_le (hBJ.trans hJT)) hBV
    have hE2 : IsPGroup 2 ((D i).img (Bf i)) :=
      ((hT.2.1.to_le (hBJ.trans hJT)).comap_of_injective _ (nLV (X i) V).subtype_injective).map _
    rw [card_eq_two_pow_of_isPGroup hE2] at hBq
    have hrk : rk ↥((D i).img (Bf i)) = n := Nat.pow_right_injective (le_refl 2) hBq
    rw [card_eq_two_pow_of_isPGroup hB2]
    congr 1
    omega

end burnsideB610_Fam

end CFSG.Quasithin.B610T
