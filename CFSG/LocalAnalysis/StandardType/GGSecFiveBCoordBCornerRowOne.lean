module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerSign
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrType
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperNbr
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSp
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSignedCoordReflGroup

public section

namespace CFSG.StandardType

open GGQ2Frame

private theorem admissible_symplectic_zero_erase {t : ℕ} (ht : 4 ≤ t) (i : Fin t) :
    PlaneRaw.admissible .symplectic (.zero (Finset.univ.erase i)) := by
  have hcard : (Finset.univ.erase i : Finset (Fin t)).card = t - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  simp only [PlaneRaw.admissible, hcard]
  omega

private theorem normalizerOf_symplectic_zero_erase {t : ℕ} (ht : 4 ≤ t) (i : Fin t) :
    PlaneRaw.normalizerOf .symplectic t (.zero (Finset.univ.erase i)) =
      PlaneRaw.signedPermGroupOn t (Finset.univ.erase i) := by
  have hcard : (Finset.univ.erase i : Finset (Fin t)).card = t - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  simp only [PlaneRaw.normalizerOf]
  rw [if_neg]
  omega

private theorem corner_normalizer_eq {G : Type} [Group G] {Bs L : Subgroup G} {n : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (hn : 5 ≤ n) (k : Fin (n - 1)) :
    (ggAutomizer (R.component (.zero (Finset.univ.erase k))) (Bs.subgroupOf L)).map
        (ggLin (p := 3) R.coord) =
      PlaneRaw.signedPermGroupOn (n - 1) (Finset.univ.erase k) := by
  classical
  have ha : (planeEntry .symplectic (n - 1)).admissible (.zero (Finset.univ.erase k)) :=
    ⟨by omega, admissible_symplectic_zero_erase (by omega) k⟩
  rw [R.normalizer_eq (.zero (Finset.univ.erase k)) ha]
  change PlaneRaw.normalizerOf .symplectic (n - 1) (.zero (Finset.univ.erase k)) =
    PlaneRaw.signedPermGroupOn (n - 1) (Finset.univ.erase k)
  exact normalizerOf_symplectic_zero_erase (by omega) k

private theorem corner_sign_mem {G : Type} [Group G] {Bs L J : Subgroup G} {n : ℕ}
    {k : Fin (n - 1)}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (hn : 5 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (J0 : Subgroup ↥L) (hJ : J = J0.map L.subtype)
    (hJ0 : J0 = R.component (.zero (Finset.univ.erase k)))
    (ι : Fin (n - 1) → Fin n) (hιsign : ∀ (J' : Subgroup ↥L) (l : Fin (n - 1)),
      PlaneRaw.negEquiv (n - 1) l ∈
          (ggAutomizer J' (Bs.subgroupOf L)).map (ggLin (p := 3) R.coord) →
        SpCoord.sgnAut (ι l) ∈
          (ggAutomizer (J'.map L.subtype) Bs).map (MulAut.congr eta).toMonoidHom)
    (l : Fin (n - 1)) (hl : l ≠ k) :
    SpCoord.sgnAut (ι l) ∈ (ggAutomizer J Bs).map (MulAut.congr eta).toMonoidHom := by
  have hmem : PlaneRaw.negEquiv (n - 1) l ∈
      (ggAutomizer (R.component (.zero (Finset.univ.erase k))) (Bs.subgroupOf L)).map
        (ggLin (p := 3) R.coord) := by
    rw [corner_normalizer_eq R hn k]
    exact Subgroup.subset_closure
      (Or.inr ⟨l, Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩, rfl⟩)
  have h := hιsign (R.component (.zero (Finset.univ.erase k))) l hmem
  rw [← hJ0, ← hJ] at h
  exact h

private theorem axis_mem_of_not_fix {n : ℕ} {i0 : Fin n} {I : Finset (Fin n)}
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod 3)))}
    (hI : Γ = bBlockOn n 3 I ∨ (2 ≤ I.card ∧ Γ = dBlockOn n 3 I))
    {v : Fin n → Multiplicative (ZMod 3)} (hv : ∀ k, k ≠ i0 → v k = 1)
    (hnot : ¬ ∀ u ∈ Γ, u v = v) : i0 ∈ I := by
  by_contra hi
  apply hnot
  intro u hu
  rcases hI with hB | ⟨hcard, hD⟩
  · rw [hB] at hu
    exact (forall_bBlockOn_fix_iff (p := 3) (by norm_num) (by norm_num) I v).mpr
      (fun i hiI => hv i (fun h => hi (h ▸ hiI))) u hu
  · rw [hD] at hu
    exact (forall_dBlockOn_fix_iff (p := 3) (by norm_num) (by norm_num) hcard v).mpr
      (fun i hiI => hv i (fun h => hi (h ▸ hiI))) u hu

private theorem coord_mem_of_sgnAut_mem {n : ℕ} {I : Finset (Fin n)}
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod 3)))}
    (hI : Γ = bBlockOn n 3 I ∨ (2 ≤ I.card ∧ Γ = dBlockOn n 3 I))
    {i : Fin n} (h : SpCoord.sgnAut i ∈ Γ) : i ∈ I := by
  by_contra hi
  let v : Fin n → Multiplicative (ZMod 3) := Pi.mulSingle i (Multiplicative.ofAdd 1)
  have hv : v = Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3)) := rfl
  have hfix : ∀ u ∈ Γ, u v = v := by
    intro u hu
    rcases hI with hB | ⟨hcard, hD⟩
    · rw [hB] at hu
      refine (forall_bBlockOn_fix_iff (p := 3) (by norm_num) (by norm_num) I v).mpr ?_ u hu
      intro j hjI
      rw [hv, Pi.mulSingle_eq_of_ne (fun hji => hi (by simpa [hji] using hjI))]
    · rw [hD] at hu
      refine (forall_dBlockOn_fix_iff (p := 3) (by norm_num) (by norm_num) hcard v).mpr ?_ u hu
      intro j hjI
      rw [hv, Pi.mulSingle_eq_of_ne (fun hji => hi (by simpa [hji] using hjI))]
  have hcoord : v i = (v i)⁻¹ := by
    have h' := congrArg (fun w : Fin n → Multiplicative (ZMod 3) => w i) (hfix _ h)
    rw [SpCoord.sgnAut_apply, Function.update_self] at h'
    exact h'.symm
  have hzero : Multiplicative.toAdd (v i) = 0 :=
    SpCoord.coord_eq_zero_of_eq_neg (p := 3) (by norm_num) (by norm_num)
      (congrArg Multiplicative.toAdd hcoord)
  have hvi : Multiplicative.toAdd (v i) = 1 := by rw [hv]; simp
  rw [hvi] at hzero
  exact SpCoord.coord_zero_ne_one (p := 3) (by norm_num) hzero.symm

private theorem aPermutationOn_le_aPermutationFull (n p : ℕ) (I : Finset (Fin n)) :
    aPermutationOn n p I ≤ aPermutationFull n p := by
  unfold aPermutationOn
  refine (Subgroup.closure_le (aPermutationFull n p)).mpr ?_
  rintro r ⟨a, -, b, -, hab, rfl⟩
  exact Subgroup.subset_closure ⟨a, b, hab, rfl⟩

theorem diagAut_mem_bSignedFull {n : ℕ} {d : Fin n → ZMod 3}
    (hd : ∀ i, d i * d i = 1) : SpCoord.diagAut d hd ∈ bSignedFull n 3 := by
  refine SpCoord.mem_of_diag (H := bSignedFull n 3) ?_ Finset.univ (SpCoord.diagAut d hd) d
    (fun i => (mul_self_eq_one_iff (a := d i)).mp (hd i))
    (fun i hi => absurd (Finset.mem_univ i) hi)
    (fun f i => by rw [SpCoord.diagAut_apply, toAdd_ofAdd])
  intro i
  exact Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)

private theorem isSignedBlockOn_b_or_d {n : ℕ} {I : Finset (Fin n)}
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod 3)))}
    (h : IsSignedBlockOn n 3 I Γ) (hsgn : ∃ i : Fin n, SpCoord.sgnAut i ∈ Γ) :
    Γ = bBlockOn n 3 I ∨ (2 ≤ I.card ∧ Γ = dBlockOn n 3 I) := by
  rcases h with hB | hD | ⟨d, hd, hSig⟩
  · exact Or.inl hB
  · exact Or.inr hD
  · exfalso
    obtain ⟨i, hi⟩ := hsgn
    have hle : (aPermutationOn n 3 I).map (MulAut.conj (SpCoord.diagAut d hd)).toMonoidHom ≤
        coordProdStab n 3 :=
      le_trans (Subgroup.map_mono (f := (MulAut.conj (SpCoord.diagAut d hd)).toMonoidHom)
        (aPermutationOn_le_aPermutationFull n 3 I))
        (aPermutationFull_map_conj_le_coordProdStab (diagAut_mem_bSignedFull hd))
    exact sgnAut_not_mem_coordProdStab (p := 3) (n := n) (by norm_num) (by norm_num) i
      (hle (hSig ▸ hi))

private theorem block_ne_univ {n : ℕ} {I : Finset (Fin n)}
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod 3)))}
    (hI : Γ = bBlockOn n 3 I ∨ (2 ≤ I.card ∧ Γ = dBlockOn n 3 I))
    {w : Fin n → Multiplicative (ZMod 3)} (hw : w ≠ 1)
    (hfix : ∀ u ∈ Γ, u w = w) : I ≠ Finset.univ := by
  intro hIuniv
  have hbd : Γ = bBlockOn n 3 Finset.univ ∨
      (2 ≤ (Finset.univ : Finset (Fin n)).card ∧ Γ = dBlockOn n 3 Finset.univ) := by
    rcases hI with hB | ⟨hcard, hD⟩
    · exact Or.inl (by rw [hB, hIuniv])
    · exact Or.inr ⟨by rwa [hIuniv] at hcard, by rw [hD, hIuniv]⟩
  apply hw
  funext i
  rcases hbd with hB | ⟨hcard, hD⟩
  · refine (forall_bBlockOn_fix_iff (p := 3) (by norm_num) (by norm_num) Finset.univ w).mp
      ?_ i (Finset.mem_univ i)
    intro u hu
    exact hfix u (by rw [hB]; exact hu)
  · refine (forall_dBlockOn_fix_iff (p := 3) (by norm_num) (by norm_num) hcard w).mp
      ?_ i (Finset.mem_univ i)
    intro u hu
    exact hfix u (by rw [hD]; exact hu)

private theorem block_eq_erase {n : ℕ} {I : Finset (Fin n)} {ι : Fin (n - 1) → Fin n}
    {k : Fin (n - 1)} (hsub : Finset.univ.erase (ι k) ⊆ I) (hne : I ≠ Finset.univ) :
    I = Finset.univ.erase (ι k) := by
  refine Finset.Subset.antisymm ?_ hsub
  intro i hiI
  rw [Finset.mem_erase]
  refine ⟨?_, Finset.mem_univ i⟩
  intro hik
  apply hne
  apply Finset.eq_univ_of_forall
  intro x
  by_cases hx : x = ι k
  · rw [hx, ← hik]; exact hiI
  · exact hsub (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)

private theorem corner_nonempty {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {n : ℕ}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3)
    {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0) :
    ∃ K, K ∈ 𝒦 := by
  have hcfg := hR
  by_contra h
  have hne : 𝒦 = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun K hK => h ⟨K, hK⟩)
  have hbs : bSignedFull n 3 = bCoordinateBlock n 3 i0 := by
    rw [← hEta, hne]
    have hjoin : ggAutomizerJoin L Bs (∅ : Finset (Subgroup G)) = ggAutomizer L Bs := by
      simp [ggAutomizerJoin]
    rw [hjoin, hb]
  exact sgnAut_not_mem_bCoordinateBlock (p := 3) (n := n) (by norm_num) (by norm_num) i0
    (by rw [← hbs]; exact Subgroup.subset_closure (Or.inl ⟨i0, rfl⟩))

private theorem eta_ne_one_of_ne_one {Bs : Type} [Group Bs] {n : ℕ}
    (eta : Bs ≃* (Fin n → Multiplicative (ZMod 3))) {b : Bs} (hb : b ≠ 1) :
    eta b ≠ 1 := by
  intro h
  apply hb
  exact eta.injective (by rw [h, map_one])

private theorem eta_coe_ne_one {G : Type} [Group G] {Bs : Subgroup G} {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {b : ↥Bs} (hb : (b : G) ≠ 1) :
    eta b ≠ 1 := by
  apply eta_ne_one_of_ne_one eta
  intro h
  exact hb (by simpa using congrArg Subtype.val h)

private theorem ggAutomizer_le_join_of_mem {G : Type} [Group G] {L Bs K : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hK : K ∈ 𝒦) :
    ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
  rw [ggAutomizerJoin]
  exact le_sup_of_le_right (le_iSup₂_of_le K hK le_rfl)

private theorem corner_component_elem {G : Type} [Group G] {Bs L : Subgroup G} {n : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (hn : 5 ≤ n) (hBs : CFSG.Open.IsElemAbelian 3 Bs) (k : Fin (n - 1)) :
    ∃ a : ↥(Bs.subgroupOf L), ((a : ↥L)) ∈ R.component (.zero (Finset.univ.erase k)) ∧
      a ≠ 1 ∧ a ^ 3 = 1 := by
  classical
  obtain ⟨l, hl⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin (n - 1))
    (by rw [Fintype.card_fin]; omega) k
  let a : ↥(Bs.subgroupOf L) := Additive.toMul (R.coord.symm (Pi.single l (1 : ZMod 3)))
  have hcoord : R.coord (Additive.ofMul a) = (Pi.single l (1 : ZMod 3) : PlaneRaw.V (n - 1)) := by
    have h : R.coord (R.coord.symm ((Pi.single l (1 : ZMod 3) : PlaneRaw.V (n - 1)))) =
        (Pi.single l (1 : ZMod 3) : PlaneRaw.V (n - 1)) :=
      AddEquiv.apply_symm_apply R.coord _
    simpa [a] using h
  have hadm : (planeEntry .symplectic (n - 1)).admissible (.zero (Finset.univ.erase k)) :=
    ⟨by omega, admissible_symplectic_zero_erase (by omega) k⟩
  have hmem : (Pi.single l (1 : ZMod 3) : PlaneRaw.V (n - 1)) ∈
      ggLinImage (p := 3) R.coord (R.component (.zero (Finset.univ.erase k))) := by
    rw [R.inside_eq (.zero (Finset.univ.erase k)) hadm]
    change (Pi.single l (1 : ZMod 3) : PlaneRaw.V (n - 1)) ∈
      PlaneRaw.insideZero (Finset.univ.erase k)
    refine (PlaneRaw.mem_insideZero' (Finset.univ.erase k) _).mpr ?_
    intro i hi
    have hil : i ≠ l := by
      intro h
      rw [h] at hi
      exact hi (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩)
    exact Pi.single_eq_of_ne hil _
  have haJ : ((a : ↥L)) ∈ R.component (.zero (Finset.univ.erase k)) :=
    (mem_ggLinImage (p := 3) R.coord (R.component (.zero (Finset.univ.erase k)))
      (Pi.single l (1 : ZMod 3) : PlaneRaw.V (n - 1))).mp hmem
  refine ⟨a, haJ, ?_, ?_⟩
  · intro h
    have h0 : (Pi.single l (1 : ZMod 3) : PlaneRaw.V (n - 1)) = 0 := by
      rw [← hcoord, h]
      exact map_zero R.coord
    have h1 : (1 : ZMod 3) = 0 := by
      simpa using congrArg (fun v : PlaneRaw.V (n - 1) => v l) h0
    exact SpCoord.coord_zero_ne_one (p := 3) (by norm_num) h1.symm
  · apply Subtype.ext
    apply Subtype.ext
    simpa using hBs.2 (((a : ↥L) : G)) (Subgroup.mem_subgroupOf.mp a.2)

private theorem corner_three_dvd_card {G : Type} [Group G] {Bs L J : Subgroup G} {n : ℕ}
    {k : Fin (n - 1)}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (hn : 5 ≤ n) (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hJ : J = (R.component (.zero (Finset.univ.erase k))).map L.subtype) :
    3 ∣ Nat.card J := by
  obtain ⟨a, haJ, ha1, ha3⟩ := corner_component_elem R hn hBs k
  have horder : orderOf a = 3 := by
    have hdvd : orderOf a ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr ha3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd h (by rwa [orderOf_eq_one_iff])
    · exact h
  have hdvdorder : orderOf (⟨(a : ↥L), haJ⟩ :
      ↥(R.component (.zero (Finset.univ.erase k)))) ∣
      Nat.card (R.component (.zero (Finset.univ.erase k))) := orderOf_dvd_natCard _
  have h3 : orderOf (⟨(a : ↥L), haJ⟩ :
      ↥(R.component (.zero (Finset.univ.erase k)))) = 3 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, horder]
  rw [hJ, Subgroup.card_map_of_injective L.subtype_injective]
  rwa [h3] at hdvdorder

private theorem corner_block_dichotomy {n : ℕ} {I : Finset (Fin n)}
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod 3)))}
    {ι : Fin (n - 1) → Fin n} {k : Fin (n - 1)} {i0 : Fin n}
    {v w : Fin n → Multiplicative (ZMod 3)}
    (hIsb : IsSignedBlockOn n 3 I Γ) (hsgn : ∃ i : Fin n, SpCoord.sgnAut i ∈ Γ)
    (hv : ∀ j, j ≠ i0 → v j = 1) (hnot : ¬ ∀ u ∈ Γ, u v = v)
    (hw : w ≠ 1) (hfix : ∀ u ∈ Γ, u w = w)
    (himg : ∀ i, i ≠ i0 → ∃ l, ι l = i)
    (hsgnK : ∀ l, l ≠ k → SpCoord.sgnAut (ι l) ∈ Γ) :
    Γ = bBlockOn n 3 (Finset.univ.erase (ι k)) ∨
      (2 ≤ (Finset.univ.erase (ι k)).card ∧
        Γ = dBlockOn n 3 (Finset.univ.erase (ι k))) := by
  have hIbd := isSignedBlockOn_b_or_d hIsb hsgn
  have hi0I := axis_mem_of_not_fix hIbd hv hnot
  have hsub : Finset.univ.erase (ι k) ⊆ I := by
    intro i hi
    rw [Finset.mem_erase] at hi
    obtain ⟨hik, -⟩ := hi
    by_cases hii0 : i = i0
    · rwa [hii0]
    · obtain ⟨l, hl⟩ := himg i hii0
      rw [← hl]
      refine coord_mem_of_sgnAut_mem hIbd (hsgnK l ?_)
      intro hlk
      exact hik (by rw [← hl, hlk])
  have hneuniv := block_ne_univ hIbd hw hfix
  have hIeq := block_eq_erase hsub hneuniv
  rcases hIbd with hB | ⟨hcard, hD⟩
  · exact Or.inl (by rw [hB, hIeq])
  · exact Or.inr ⟨by rwa [hIeq] at hcard, by rw [hD, hIeq]⟩

private theorem corner_eta_setup {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {n : ℕ}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hxL' : Subgroup.zpowers x ⊓ L = ⊥)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (k : Fin (n - 1))
    (hJ : J = (R.component (.zero (Finset.univ.erase k))).map L.subtype) :
    ∃ (xb : ↥Bs) (ι : Fin (n - 1) → Fin n),
      (xb : G) = x ∧ (∀ j, j ≠ i0 → eta xb j = 1) ∧ eta xb i0 ≠ 1 ∧
      (∀ k' : Fin (n - 1), ι k' ≠ i0) ∧ (∀ i, i ≠ i0 → ∃ l, ι l = i) ∧
      (∀ l, l ≠ k → SpCoord.sgnAut (ι l) ∈
        (ggAutomizer J Bs).map (MulAut.congr eta).toMonoidHom) := by
  obtain ⟨-, hxB, hxne1, hcomp, -⟩ := hR.1.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hR.1.1.2.1.1 hxB
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((Subgroup.mem_centralizer_iff.mp (hcomp.1 hl)) x (Set.mem_singleton x)).symm
  obtain ⟨ι, -, hιne, hιsurj, -, hιsign⟩ :=
    exists_eta_frame_of_realization (n := n) (by omega) hR.1.1.2.1.2.1 hxBs hxL hxL' hsplit R eta hb
  let xb : ↥Bs := ⟨x, hxBs⟩
  have hxaxis : eta xb = Pi.mulSingle i0 (eta xb i0) :=
    eta_eq_mulSingle_of_mem_centralizer (i0 := i0) eta hb hxL
  refine ⟨xb, ι, rfl, ?_, ?_, hιne, hιsurj, ?_⟩
  · intro j hj
    rw [hxaxis, Pi.mulSingle_eq_of_ne hj]
  · intro h1
    apply hxne1
    have h2 : xb = 1 := by
      apply eta.injective
      funext j
      rw [map_one, Pi.one_apply]
      by_cases hj : j = i0
      · rw [hj, hxaxis]
        simpa using h1
      · rw [hxaxis, Pi.mulSingle_eq_of_ne hj]
    exact congrArg Subtype.val h2
  · intro l hl
    exact corner_sign_mem R hn eta (R.component (.zero (Finset.univ.erase k))) hJ rfl ι hιsign l hl

theorem GGSecFiveRouteCfg.exists_bCoordinateBlock_of_cornerRowOne {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hLB : GGLBalanceInput)
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {n : ℕ} (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3)
    {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hxL' : Subgroup.zpowers x ⊓ L = ⊥)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    {k : Fin (n - 1)} (hJ : J = (R.component (.zero (Finset.univ.erase k))).map L.subtype) :
    ∃ K ∈ 𝒦, ∃ j : Fin n, j ≠ i0 ∧ J ≤ K ∧
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 j := by
  classical
  obtain ⟨xb, ι, hxb, hxsupp, hx0, hιne, hιsurj, hsignJ⟩ :=
    corner_eta_setup hR hn eta hb hxL' hsplit R k hJ
  have h3dvdJ : 3 ∣ Nat.card J := corner_three_dvd_card R hn hR.1.1.2.1.2.1 hJ
  obtain ⟨K, hK⟩ := corner_nonempty hR eta hEta hb
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK
  have hKle := ggAutomizer_le_join_of_mem (L := L) (Bs := Bs) hK
  have hJK : J ≤ K := le_of_ggNbr hLB hR.1.1.1 hR.1.1.2.2 h3dvdJ hnb
  have hyBs : y ∈ Bs := hR.1.1.2.1.1 hnb.1.2.1
  let yb : ↥Bs := ⟨y, hyBs⟩
  have hdatum := hR.signedNbrDatum hX hTCJ hRig hTPn hA8 hraw hiso hFC eta hEta hnb hKle
    (xb := xb) (yb := yb) hxb rfl
  obtain ⟨I, hIsb⟩ := hdatum.isSignedBlockOn
  obtain ⟨l0, hl0⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin (n - 1))
    (by rw [Fintype.card_fin]; omega) k
  have hsignK : ∀ l : Fin (n - 1), l ≠ k →
      SpCoord.sgnAut (ι l) ∈ (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom :=
    fun l hl => Subgroup.map_mono
      (f := (MulAut.congr eta).toMonoidHom) (ggAutomizer_mono Bs hJK) (hsignJ l hl)
  have hdisj := corner_block_dichotomy hIsb ⟨ι l0, hsignK l0 hl0⟩ hxsupp hdatum.not_fix
    (eta_coe_ne_one eta hnb.1.2.2.1) hdatum.fix hιsurj hsignK
  refine ⟨K, hK, ι k, hιne k, hJK, ?_⟩
  rcases hdisj with hB | ⟨hcard, hD⟩
  · rw [hB, bBlockOn_univ_erase]
  · exact ggAutomizer_eq_bCoordinateBlock_of_common_sgn (hp := by norm_num) (hp2 := by norm_num)
      hJK eta (ι k) (Or.inr (Or.inl ⟨hcard, hD⟩)) (hsignJ l0 hl0)

end CFSG.StandardType
