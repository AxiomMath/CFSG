module

public import CFSG.Walter.Bender1970.S38.NotCyclic
public import CFSG.Walter.Bender1970.S4.ComponentTools
public import CFSG.Walter.Bender1970.S4.Types

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

@[expose] def NoJRComponents (G : Type) [Group G] [Finite G] : Prop :=
  ∀ s : G, orderOf s = 2 → ∀ M ∈ benderM s, ∀ J : Subgroup G, IsComponentOf J M →
    ¬ IsTypeJR (J ⧸ Subgroup.center J)

namespace Bender44

@[expose] def Admissible (K J : Subgroup G) : Prop :=
  IsTypeJR (K ⧸ Subgroup.center K) → ¬ IsTypeL2Odd (J ⧸ Subgroup.center J)

omit [Finite G] in
theorem admissible_map_conj {K J : Subgroup G} (g : G) (h : Admissible K J) :
    Admissible K (J.map (MulAut.conj g).toMonoidHom) := fun hK hJ =>
  h hK ((isTypeL2Odd_map_conj_iff J g).mp hJ)

theorem admissible_self (K : Subgroup G) : Admissible K K := fun hK =>
  not_isTypeL2Odd_of_isTypeJR hK

variable (hG : BenderCounterexample G)
include hG

theorem isComponentOf_of_le_of_mem_benderM
    {x : G} (hx : orderOf x = 2) {X : Subgroup G}
    (hX : X ∈ benderM x) {y : G} (hy : orderOf y = 2) {Y : Subgroup G} (hY : Y ∈ benderM y)
    (hxY : x ∈ Y) {J : Subgroup G} (hJ : IsComponentOf J X) (hJY : J ≤ Y)
    (hres : ¬ IsTypeL2Odd (J ⧸ Subgroup.center J) ∨ NoJRComponents G) : IsComponentOf J Y := by
  have hXA := hG.isAStar_of_isCoatom (isCoatom_of_mem_benderM hX)
  have hYA := hG.isAStar_of_isCoatom (isCoatom_of_mem_benderM hY)
  obtain ⟨J', hJ', -, h⟩ := exists_isComponentOf_of_le hXA.1 hYA (bender1970_4_3 hG hy hY)
    (mem_of_mem_benderM hX) hxY hx (inf_le_right.trans (centralizer_le_of_mem_benderM hX)) hJ
    hJY
  rcases h with rfl | ⟨hJ2, hJ'JR, -⟩
  · exact hJ'
  · rcases hres with h | h
    · exact absurd hJ2 h
    · exact absurd hJ'JR (h y hy Y hY J' hJ')

theorem exists_involution_mem_inf
    {t : G} {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G)
    (htT : t ∈ (T : Subgroup G)) {K : Subgroup G} (hK : IsComponentOf K H) :
    ∃ k ∈ (T : Subgroup G) ⊓ K, orderOf k = 2 := by
  have hKQ := hG.bender38Component' hH T htT hK
  obtain ⟨k, hk, hk1, -⟩ := exists_mem_ne_one_ne (Q := (T : Subgroup G) ⊓ K)
    (by have := hKQ.four_le_card; omega) 1
  exact ⟨k, hk, orderOf_eq_prime (hKQ.sq_eq_one k hk) hk1⟩

theorem centralizer_le
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t)
    (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) {K : Subgroup G} (hK : IsComponentOf K H)
    (hres : IsTypeJR (K ⧸ Subgroup.center K) ∨ NoJRComponents G) :
    Subgroup.centralizer (K : Set G) ≤ H ∧
      Subgroup.normalizer ((sSup {J | IsComponentOf J H ∧ Admissible K J} : Subgroup G) :
        Set G) = H ∧
      sSup {J | IsComponentOf J H ∧ Admissible K J} =
        K ⊔ sSup {J | IsComponentOf J (Subgroup.centralizer (K : Set G)) ∧ Admissible K J} := by
  have := hG.isSimpleGroup
  obtain ⟨k, hk, hk2⟩ := exists_involution_mem_inf hG hH T htT hK
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hk2
    omega
  obtain ⟨M, hM⟩ := hG.benderM_nonempty hk1
  have hTM := hG.sylow_le_of_mem_benderM T hk.1 hM
  have hCM : Subgroup.centralizer (K : Set G) ≤ M :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hk.2)).trans
      (centralizer_le_of_mem_benderM hM)
  refine centralizer_le_and_eq_of_forall_isComponentOf (isCoatom_of_mem_benderM hH) hK
    (Admissible K) (fun J g hJ => admissible_map_conj g hJ) (admissible_self K)
    fun J hJ hJP hJK => ?_
  have hJC : J ≤ Subgroup.centralizer (K : Set G) := le_centralizer_of_isComponentOf_ne hJ hK hJK
  have hJM := isComponentOf_of_le_of_mem_benderM hG ht hH hk2 hM (hTM htT) hJ (hJC.trans hCM)
    (hres.imp (fun h => hJP h) id)
  exact isComponentOf_of_le hJM hJC hCM

theorem eq_of_le
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t)
    (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) {K : Subgroup G} (hK : IsComponentOf K H)
    (hres : IsTypeJR (K ⧸ Subgroup.center K) ∨ NoJRComponents G) {s : G}
    (hsT : s ∈ (T : Subgroup G)) (hs : orderOf s = 2) {M : Subgroup G} (hM : M ∈ benderM s)
    (hKM : K ≤ M) : M = H := by
  have hTM := hG.sylow_le_of_mem_benderM T hsT hM
  have hKM' : IsComponentOf K M := isComponentOf_of_le_of_mem_benderM hG ht hH hs hM (hTM htT)
    hK hKM (hres.imp (fun h => admissible_self K h) id)
  obtain ⟨-, hNH, hH'⟩ := centralizer_le hG ht hH T htT hK hres
  obtain ⟨-, hNM, hM'⟩ := centralizer_le hG hs hM T hsT hKM' hres
  calc M = Subgroup.normalizer ((sSup {J | IsComponentOf J M ∧ Admissible K J} :
        Subgroup G) : Set G) := hNM.symm
    _ = Subgroup.normalizer ((sSup {J | IsComponentOf J H ∧ Admissible K J} :
        Subgroup G) : Set G) := by rw [hM', hH']
    _ = H := hNH

theorem benderM_eq_singleton
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t)
    (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) {K : Subgroup G} (hK : IsComponentOf K H)
    (hres : IsTypeJR (K ⧸ Subgroup.center K) ∨ NoJRComponents G) {s : G}
    (hsU : s ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G)) (hs : orderOf s = 2) :
    benderM s = {H} := by
  have hKs : K ≤ Subgroup.centralizer ({s} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hsU.2) k hk)
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    omega
  have key : ∀ M ∈ benderM s, M = H := fun M hM =>
    eq_of_le hG ht hH T htT hK hres hsU.1 hs hM (hKs.trans (centralizer_le_of_mem_benderM hM))
  obtain ⟨M₀, hM₀⟩ := hG.benderM_nonempty hs1
  rw [Set.eq_singleton_iff_unique_mem]
  exact ⟨key M₀ hM₀ ▸ hM₀, key⟩

theorem normalizer_le
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t)
    (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) {K : Subgroup G} (hK : IsComponentOf K H)
    (hres : IsTypeJR (K ⧸ Subgroup.center K) ∨ NoJRComponents G) :
    Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ H :=
  bender1970_3_8 hG ht hH T htT hK (fun _ hs _ hM => bender1970_4_1 hG hs hM)
    fun _ hsU hs => benderM_eq_singleton hG ht hH T htT hK hres hsU hs

theorem not_isCyclic
    {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t)
    (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G)) {K : Subgroup G} (hK : IsComponentOf K H) :
    ¬ IsCyclic ((T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) :=
  bender1970_3_8_not_isCyclic hG ht hH T htT hK fun _ hs _ hM => bender1970_4_1 hG hs hM

end Bender44

end CFSG.Walter
