module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrType
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrameClass
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniModelTwoCenter
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperNbr
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperRootModel
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves
import CFSG.LocalAnalysis.StandardType.GGSignedCoordReflGroup
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem isBlockOn_finset_mono {K : Type} [Field K] {d : ℕ} {S T : Finset (Fin d)}
    {M : Matrix (Fin d) (Fin d) K} (hST : S ⊆ T) (h : TableBUE.IsBlockOn S M) :
    TableBUE.IsBlockOn T M := by
  intro a b hab
  exact h a b (hab.imp (fun ha hS => ha (hST hS)) (fun hb hS => hb (hST hS)))

private theorem exists_diag_blockSU {F : Type} [Field F] {p n f : ℕ}
    (hfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F)
    (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1) {I : Finset (Fin n)} {i j : Fin n}
    (hiI : i ∈ I) (hjI : j ∈ I) (hij : i ≠ j) :
    ∃ (u : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F n)) (t : Fin n → Fˣ) (ζ : Fˣ),
      orderOf ζ = p ∧ t i = ζ ∧ t j = ζ⁻¹ ∧ (∀ k, t k ^ p = 1) ∧
        (u : GL (Fin n) F) = SectionRank.OddCover.diagHom n t ∧
        u ∈ TableBUE.blockSU (K := F) (n := f) I := by
  classical
  obtain ⟨ζ, hζord, hζnorm⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one hfield hp hpq
  have hζp : ζ ^ p = 1 := hζord ▸ pow_orderOf_eq_one ζ
  set t : Fin n → Fˣ := Pi.mulSingle i ζ * Pi.mulSingle j ζ⁻¹ with ht
  have ht_i : t i = ζ := by simp [ht, Pi.mulSingle, hij]
  have ht_j : t j = ζ⁻¹ := by
    rw [ht, Pi.mul_apply, Pi.mulSingle_eq_of_ne (Ne.symm hij), Pi.mulSingle_eq_same, one_mul]
  have ht_off : ∀ k, k ≠ i → k ≠ j → t k = 1 :=
    fun k hki hkj => by simp [ht, Pi.mulSingle, hki, hkj]
  have ht_pow : ∀ k, t k ^ p = 1 := by
    intro k
    obtain rfl | hki := eq_or_ne k i
    · rw [ht_i, hζp]
    obtain rfl | hkj := eq_or_ne k j
    · rw [ht_j, inv_pow, hζp, inv_one]
    rw [ht_off k hki hkj, one_pow]
  have ht_norm : ∀ k, t k ^ (2 ^ f + 1) = 1 := by
    intro k
    obtain rfl | hki := eq_or_ne k i
    · rw [ht_i]; exact hζnorm
    obtain rfl | hkj := eq_or_ne k j
    · rw [ht_j, inv_pow, hζnorm, inv_one]
    rw [ht_off k hki hkj, one_pow]
  have ht_prod : ∏ k, t k = 1 := by
    rw [ht]
    simp only [Pi.mul_apply, Finset.prod_mul_distrib]
    rw [Finset.prod_eq_single i (fun k _ hk => by simp [Pi.mulSingle, hk])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [Finset.prod_eq_single j (fun k _ hk => by simp [Pi.mulSingle, hk])
      (fun h => absurd (Finset.mem_univ j) h)]
    simp
  have hmem : SectionRank.OddCover.diagHom n t ∈
      CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F n :=
    TableBUE.diagHom_mem_unitarySU hfield ht_norm ht_prod
  refine ⟨⟨SectionRank.OddCover.diagHom n t, hmem⟩, t, ζ, hζord, ht_i, ht_j, ht_pow, rfl, ?_⟩
  rw [TableBUE.mem_blockSU, SectionRank.OddCover.coe_diagHom]
  intro a b hab; by_cases hab' : a = b
  · subst hab'; have haI : a ∉ I := hab.elim id id
    rw [Matrix.diagonal_apply_eq,
      ht_off a (fun h => haI (h ▸ hiI)) (fun h => haI (h ▸ hjI)),
      Matrix.one_apply_eq, Units.val_one]
  · rw [Matrix.diagonal_apply_ne _ hab', Matrix.one_apply_ne hab']

private theorem frame_p_exists {G F : Type} [Group G] [Field F] {p n f : ℕ}
    {Bs L J : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ}
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) {I : Finset (Fin n)}
    (hI2 : 2 ≤ I.card) (hJI : J = (TableBUE.blockSU (K := F) (n := f) I).map σ) :
    ∃ s ∈ J, s ^ p = 1 ∧ s ≠ 1 := by
  classical
  obtain ⟨i, hiI, j, hjI, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < I.card)
  obtain ⟨u, t, ζ, hζord, hti, htj, htp, huval, hub⟩ :=
    exists_diag_blockSU hfield hp hpq hiI hjI hij
  have hup : u ^ p = 1 := by
    refine Subtype.ext ?_
    show ((u : GL (Fin n) F)) ^ p = 1
    have htp' : t ^ p = 1 := funext htp
    rw [huval, ← map_pow, htp', map_one]
  refine ⟨σ u, ?_, ?_, ?_⟩
  · rw [hJI]; exact Subgroup.mem_map.mpr ⟨u, hub, rfl⟩
  · rw [← map_pow, hup, map_one]
  · intro h1
    obtain ⟨c, hc⟩ := hLF.2.1 u h1
    have hc' : (((SectionRank.OddCover.diagHom n t : GL (Fin n) F)) :
        Matrix (Fin n) (Fin n) F) = Matrix.diagonal (fun _ => c) := by
      rw [← huval]; exact hc
    rw [SectionRank.OddCover.coe_diagHom] at hc'
    have h1i : ((t i : F)) = c := by
      have h := congrFun (congrFun hc' i) i
      simpa [Matrix.diagonal_apply_eq] using h
    have h1j : ((t j : F)) = c := by
      have h := congrFun (congrFun hc' j) j
      simpa [Matrix.diagonal_apply_eq] using h
    have hζeq : ζ = ζ⁻¹ := by
      refine Units.ext ?_
      have h2 : ((t i : F)) = ((t j : F)) := by rw [h1i, h1j]
      rwa [hti, htj] at h2
    have h2 : ζ ^ 2 = 1 := by
      have h3 : ζ * ζ = 1 := by nth_rewrite 2 [hζeq]; exact mul_inv_cancel ζ
      simpa [pow_two] using h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hζord ▸
      orderOf_dvd_of_pow_eq_one h2))

private theorem dvd_card_J_of_frame {G F : Type} [Group G] [Field F] {p n f : ℕ}
    {Bs L J : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ}
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) {I : Finset (Fin n)}
    (hI2 : 2 ≤ I.card) (hJI : J = (TableBUE.blockSU (K := F) (n := f) I).map σ) :
    p ∣ Nat.card J := by
  obtain ⟨s, hsJ, hsp, hs1⟩ := frame_p_exists hLF hfield hp hp2 hpq hI2 hJI
  have h := orderOf_dvd_natCard (⟨s, hsJ⟩ : ↥J)
  rwa [Subgroup.orderOf_mk, orderOf_eq_prime (hp := ⟨hp⟩) hsp hs1] at h

private theorem class_card {G F : Type} [Group G] [Field F] {p n f : ℕ}
    {B Bs : Subgroup G} {L D J : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ} {I : Finset (Fin n)}
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hDBs : D ≤ Bs) (hJeq : D = B ⊓ Subgroup.centralizer (J : Set G))
    (hJI : J = (TableBUE.blockSU (K := F) (n := f) I).map σ)
    (hconst : ∀ b : ↥Bs, (b : G) ∈ D → ∀ i ∈ I, ∀ j ∈ I, eta b i = eta b j)
    {a a' : Fin n} (haI : a ∈ I) (ha'I : a' ∈ I)
    (hroot : ∀ b : ↥Bs, (b : G) ∈ B ↔ eta b a = eta b a') :
    Nat.card ↥D = p ^ (n - I.card + 1) := by
  have hDmem : ∀ b : ↥Bs, (b : G) ∈ D ↔ ∀ i ∈ I, ∀ j ∈ I, eta b i = eta b j := by
    intro b
    refine ⟨hconst b, fun h => ?_⟩
    rw [hJeq]
    exact ⟨(hroot b).mpr (h a haI a' ha'I), by
      rw [hJI]
      exact hLF.mem_centralizer_map_blockSU_of_const b h⟩
  have hcardD : Nat.card ↥D = Nat.card {v : Fin n → Multiplicative (ZMod p) //
      ∀ i ∈ I, ∀ j ∈ I, v i = v j} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun d => ⟨eta ⟨(d : G), hDBs d.2⟩, fun i hi j hj => ?_⟩
        invFun := fun v => ⟨((eta.symm v.1 : ↥Bs) : G), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · exact hconst ⟨(d : G), hDBs d.2⟩ d.2 i hi j hj
    · rw [hDmem]
      intro i hi j hj
      simpa only [MulEquiv.apply_symm_apply] using v.2 i hi j hj
    · intro d; apply Subtype.ext; simp
    · intro v; apply Subtype.ext; simp
  have hcardS : Nat.card {v : Fin n → Multiplicative (ZMod p) //
      ∀ i ∈ I, ∀ j ∈ I, v i = v j} = p ^ (n - I.card + 1) := by
    have e : {v : Fin n → Multiplicative (ZMod p) // ∀ i ∈ I, ∀ j ∈ I, v i = v j} ≃
        {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ aPermutationOn n p I, u f = f} :=
      Equiv.subtypeEquivRight fun f => (forall_aPermutationOn_fix_iff I f).symm
    rw [Nat.card_congr e]
    exact card_fix_aPermutationOn ⟨a, haI⟩
  rw [hcardD, hcardS]

private theorem class_erase {G : Type} [Group G] {p n : ℕ} {D : Subgroup G} {I : Finset (Fin n)}
    (hp : p.Prime) (hDcard : Nat.card ↥D = p ^ 2)
    (hcard : Nat.card ↥D = p ^ (n - I.card + 1)) : ∃ k : Fin n, I = Finset.univ.erase k := by
  have hk2 : n - I.card + 1 = 2 := by
    have h1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (le_of_eq (hcard.symm.trans hDcard))
    have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (le_of_eq (hDcard.symm.trans hcard))
    omega
  have hIcard : I.card = n - 1 := by
    have hle : I.card ≤ n := by simpa using Finset.card_le_univ I
    omega
  have hkI : ∃ k : Fin n, k ∉ I := by
    by_contra h
    push Not at h
    have hle := Finset.card_le_card (s := Finset.univ) (t := I) fun t _ => h t
    rw [Finset.card_univ, Fintype.card_fin] at hle
    omega
  obtain ⟨k, hk⟩ := hkI
  refine ⟨k, ?_⟩
  have hsub : I ⊆ Finset.univ.erase k := fun t ht =>
    Finset.mem_erase.mpr ⟨fun h => hk (h ▸ ht), Finset.mem_univ t⟩
  have hcard' : (Finset.univ.erase k).card ≤ I.card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    omega
  exact Finset.eq_of_subset_of_card_le hsub hcard'

private theorem anchor_data {G : Type} [Group G] [Finite G] {p n : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hTBF : GGTBFixInput) (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hLB : GGLBalanceInput) (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B ≠ Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpJ : p ∣ Nat.card J) :
    ∃ (K₀ : Subgroup G) (_ : K₀ ∈ 𝒦) (I₀ : Finset (Fin n)) (y₀b : ↥Bs),
      I₀.Nonempty ∧ (y₀b : G) ∈ B ∧
        (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I₀ ∧
        (∀ k ∈ I₀, eta y₀b k = 1) ∧ y₀b ≠ 1 ∧ J ≤ K₀ := by
  have hL' : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p := by
    rw [hLA]; exact aPermutationFull_le_coordProdStab
  have hFr : GGBProperFrame p n B Bs L x 𝒦 (fun y K => K ∈ 𝒦 ∧ GGNbr p B x D J y K) eta :=
    hR.bProperFrame_selected hTBF hX hTCJ hRig hTPn hA8 hraw hiso hFC hB eta hEta
  obtain ⟨K₀, hK₀, I₀, hI₀ne, hA₀⟩ := hFr.exists_mem_bBlockOn hL'
  obtain ⟨y₀, hy₀⟩ := hFr.exists_nb K₀ hK₀
  have hy₀B : y₀ ∈ B := hFr.mem y₀ K₀ hy₀
  refine ⟨K₀, hK₀, I₀, ⟨y₀, hFr.le hy₀B⟩, hI₀ne, hy₀B, hA₀, ?_, ?_,
    SecFiveL1Odd.J_le hLB hR hpJ (Or.inr hK₀)⟩
  · have hdat : SignedNbrDatum n p (eta ⟨x, hFr.fixLineComp.mem⟩) (eta ⟨y₀, hFr.le hy₀B⟩)
        ((ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom) :=
      hFr.datum y₀ K₀ hy₀ ⟨x, hFr.fixLineComp.mem⟩ ⟨y₀, hFr.le hy₀B⟩ rfl rfl
    rw [← forall_bBlockOn_fix_iff hp hp2 I₀ (eta ⟨y₀, hFr.le hy₀B⟩), ← hA₀]
    exact hdat.fix
  · intro h
    refine hFr.not_mem y₀ K₀ hy₀ ?_
    rw [show y₀ = 1 from congrArg Subtype.val h]
    exact Subgroup.one_mem _

private theorem mem_D_iff_of_two {G F : Type} [Group G] [Field F] {p n : ℕ}
    {B Bs : Subgroup G} {L D J : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ} {I : Finset (Fin n)}
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hDB : D ≤ B) (hJeq : D = B ⊓ Subgroup.centralizer (J : Set G))
    (hJI : J = (TableBUE.blockSU (K := F) (n := 1) I).map σ)
    (hconst : ∀ b : ↥Bs, (b : G) ∈ D → ∀ i ∈ I, ∀ j ∈ I, eta b i = eta b j)
    {a a' : Fin n} (hroot : ∀ b : ↥Bs, (b : G) ∈ B ↔ eta b a = eta b a')
    (b : ↥Bs) :
    (b : G) ∈ D ↔ (∀ i ∈ I, ∀ j ∈ I, eta b i = eta b j) ∧ eta b a = eta b a' := by
  refine ⟨fun hb => ⟨hconst b hb, (hroot b).mp (hDB hb)⟩, fun h => ?_⟩
  rw [hJeq]
  exact ⟨(hroot b).mpr h.2, by
    rw [hJI]
    exact hLF.mem_centralizer_map_blockSU_of_const b h.1⟩

private theorem three_le_card_D_of_third {G F : Type} [Group G] [Finite G] [Field F] {p n : ℕ}
    {B Bs : Subgroup G} {L D J : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ} {I : Finset (Fin n)}
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hDB : D ≤ B) (hJeq : D = B ⊓ Subgroup.centralizer (J : Set G))
    (hJI : J = (TableBUE.blockSU (K := F) (n := 1) I).map σ)
    (hconst : ∀ b : ↥Bs, (b : G) ∈ D → ∀ i ∈ I, ∀ j ∈ I, eta b i = eta b j)
    {a a' : Fin n} (hroot : ∀ b : ↥Bs, (b : G) ∈ B ↔ eta b a = eta b a')
    (haI : a ∉ I) (ha'I : a' ∉ I) {k : Fin n} (hkI : k ∉ I)
    (hka : k ≠ a) (hka' : k ≠ a') (hI4 : 4 ≤ I.card) :
    p ^ 3 ≤ Nat.card ↥D := by
  classical
  obtain ⟨i0, hi0⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
  let v : (Fin 3 → ZMod p) → Fin n → ZMod p := fun w j =>
    if j ∈ I then w 0 else if j = a ∨ j = a' then w 1 else if j = k then w 2 else 0
  let b : (Fin 3 → ZMod p) → ↥Bs := fun w =>
    eta.symm fun j => Multiplicative.ofAdd (v w j)
  have hη : ∀ (w : Fin 3 → ZMod p) (j : Fin n),
      eta (b w) j = Multiplicative.ofAdd (v w j) := fun w j =>
    congrFun (MulEquiv.apply_symm_apply eta (fun j => Multiplicative.ofAdd (v w j))) j
  have hmem : ∀ w, (b w : G) ∈ D := by
    intro w
    refine (mem_D_iff_of_two hLF hDB hJeq hJI hconst hroot (b w)).mpr ⟨?_, ?_⟩
    · intro i hi j hj
      rw [hη, hη]
      simp only [v, if_pos hi, if_pos hj]
    · rw [hη, hη]
      simp [v, haI, ha'I]
  let emb : (Fin 3 → ZMod p) → ↥D := fun w => ⟨(b w : G), hmem w⟩
  have hinj : Function.Injective emb := by
    intro w w' hww'
    have hb : b w = b w' := Subtype.ext (congrArg (fun x : ↥D => (x : G)) hww')
    have hfun : ∀ j, Multiplicative.ofAdd (v w j) = Multiplicative.ofAdd (v w' j) := by
      intro j
      rw [← hη w j, ← hη w' j, hb]
    funext m
    fin_cases m
    · exact Multiplicative.ofAdd.injective (by simpa [v, hi0] using hfun i0)
    · exact Multiplicative.ofAdd.injective (by simpa [v, haI, ha'I] using hfun a)
    · exact Multiplicative.ofAdd.injective (by simpa [v, hkI, hka, hka'] using hfun k)
  have hle : Nat.card (Fin 3 → ZMod p) ≤ Nat.card ↥D :=
    Nat.card_le_card_of_injective emb hinj
  have hcard : Nat.card (Fin 3 → ZMod p) = p ^ 3 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  rwa [hcard] at hle

private theorem eq_compl_pair_of_two {G F : Type} [Group G] [Finite G] [Field F] {p n : ℕ}
    {B Bs : Subgroup G} {L D J : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ} {I : Finset (Fin n)}
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hDB : D ≤ B) (hJeq : D = B ⊓ Subgroup.centralizer (J : Set G))
    (hJI : J = (TableBUE.blockSU (K := F) (n := 1) I).map σ)
    (hconst : ∀ b : ↥Bs, (b : G) ∈ D → ∀ i ∈ I, ∀ j ∈ I, eta b i = eta b j)
    (hIfull : ∀ i ∈ I, ∀ j : Fin n,
      (∀ b : ↥Bs, (b : G) ∈ D → eta b j = eta b i) → j ∈ I)
    {a a' : Fin n} (hroot : ∀ b : ↥Bs, (b : G) ∈ B ↔ eta b a = eta b a')
    (hp : p.Prime) (hDcard : Nat.card ↥D = p ^ 2) (hI4 : 4 ≤ I.card) (haI : a ∉ I) :
    I = ({a, a'} : Finset (Fin n))ᶜ := by
  have ha'I : a' ∉ I := by
    intro ha'
    exact haI (hIfull a' ha' a fun b hb => (hroot b).mp (hDB hb))
  ext j
  constructor
  · intro hj
    rw [Finset.mem_compl]
    intro hmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact haI (h ▸ hj)
    · exact ha'I (h ▸ hj)
  · intro hj
    rw [Finset.mem_compl] at hj
    by_contra hjI
    have hja : j ≠ a := fun h => hj (by simp [h])
    have hja' : j ≠ a' := fun h => hj (by simp [h])
    have hle := three_le_card_D_of_third hLF hDB hJeq hJI hconst hroot haI ha'I hjI
      hja hja' hI4
    rw [hDcard] at hle
    exact absurd hle (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 2 < 3)))

private theorem anchor_eq_one {G : Type} [Group G] {p n : ℕ} {B Bs : Subgroup G}
    {a a' : Fin n} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {I I₀ : Finset (Fin n)} {y : ↥Bs}
    (hIcompl : I = ({a, a'} : Finset (Fin n))ᶜ) (hII₀ : I ⊆ I₀)
    (hroot : ∀ b : ↥Bs, (b : G) ∈ B ↔ eta b a = eta b a') (hyB : (y : G) ∈ B)
    (hyI₀ : ∀ k ∈ I₀, eta y k = 1) (ha : a ∈ I₀ ∨ a' ∈ I₀) : y = 1 := by
  have hya : eta y a = 1 := by
    rcases ha with ha | ha
    · exact hyI₀ a ha
    · rw [(hroot y).mp hyB]; exact hyI₀ a' ha
  have hya' : eta y a' = 1 := by
    rcases ha with ha | ha
    · rw [← (hroot y).mp hyB]; exact hyI₀ a ha
    · exact hyI₀ a' ha
  have hvanish : ∀ j, eta y j = 1 := by
    intro j
    by_cases hj : j ∈ ({a, a'} : Finset (Fin n))
    · rw [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact hya
      · exact hya'
    · refine hyI₀ j (hII₀ ?_)
      have hjc : j ∈ ({a, a'} : Finset (Fin n))ᶜ := by simpa using hj
      rwa [← hIcompl] at hjc
  apply eta.injective
  funext j
  simpa using hvanish j

private theorem anchor_eq_univ_erase {G : Type} [Group G] {p n : ℕ} {Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {y : ↥Bs} {I₀ : Finset (Fin n)}
    {k : Fin n} (hsub : Finset.univ.erase k ⊆ I₀) (hyfix : ∀ i ∈ I₀, eta y i = 1)
    (hyne : y ≠ 1) : I₀ = Finset.univ.erase k := by
  have hne : I₀ ≠ Finset.univ := by
    intro h
    have h1 : eta y = 1 := funext fun i => hyfix i (h ▸ Finset.mem_univ i)
    refine hyne ?_
    apply eta.injective
    simpa using h1
  have hcardK : (Finset.univ.erase k).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  have hle : I₀.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ I₀
  have hne' : I₀.card ≠ n := by
    intro h
    exact hne (Finset.eq_univ_of_card I₀ (by rwa [Fintype.card_fin]))
  have hcf : (Finset.univ.erase k).card ≤ I₀.card := Finset.card_le_card hsub
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

private theorem exists_class_data {G F : Type} [Group G] [Finite G] [Field F] [Finite F]
    [CharP F 2] {p n f : ℕ}
    {Bs : Subgroup G} {L D J : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ}
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F)
    (hf : 2 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1)
    (hDBs : D ≤ Bs)
    (hJc : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)))
    (hJL : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G))) :
    ∃ I : Finset (Fin n), 2 ≤ I.card ∧ J = (TableBUE.blockSU (K := F) (n := f) I).map σ ∧
      (∀ b : ↥Bs, (b : G) ∈ D → ∀ i ∈ I, ∀ j ∈ I, eta b i = eta b j) ∧
      (∀ i j : Fin n, i ≠ j →
        (∀ b : ↥Bs, (b : G) ∈ D → eta b i = eta b j) → i ∈ I ∧ j ∈ I) ∧
      p ∣ Nat.card J := by
  obtain ⟨I, hI2, hJI, hIconst, hIpair⟩ :=
    hLF.exists_eq_map_blockSU_of_layer (K := F) (f := f)
      hfield hf hp hpq hDBs hJc hJL
  refine ⟨I, hI2, hJI, ?_, ?_, dvd_card_J_of_frame hLF hfield hp hp2 hpq hI2 hJI⟩
  · intro b hb i hi j hj
    have hbeq : (⟨(b : G), hDBs hb⟩ : ↥Bs) = b := Subtype.ext rfl
    have h := hIconst (b : G) hb i hi j hj
    rwa [hbeq] at h
  · intro i j hij h
    exact hIpair i j hij fun d hd => h ⟨d, hDBs hd⟩ hd

private theorem exists_class_data_two {G F : Type} [Group G] [Finite G] [Field F] [Finite F]
    [CharP F 2] {p n : ℕ}
    {Bs : Subgroup G} {L D J : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ}
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ 1 + 1)
    (hDBs : D ≤ Bs)
    (hJc : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)))
    (hJL : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G))) :
    ∃ I : Finset (Fin n), 4 ≤ I.card ∧
      J = (TableBUE.blockSU (K := F) (n := 1) I).map σ ∧
      (∀ b : ↥Bs, (b : G) ∈ D → ∀ i ∈ I, ∀ j ∈ I, eta b i = eta b j) ∧
      (∀ i ∈ I, ∀ j : Fin n,
        (∀ b : ↥Bs, (b : G) ∈ D → eta b j = eta b i) → j ∈ I) ∧
      p ∣ Nat.card J := by
  obtain ⟨I, hI4, hJI, hIconst, hIfull⟩ :=
    hLF.exists_eq_map_blockSU_of_layer_two (K := F) hfield hp hpq hDBs hJc hJL
  refine ⟨I, hI4, hJI, ?_, ?_,
    dvd_card_J_of_frame hLF hfield hp hp2 hpq (by omega) hJI⟩
  · intro b hb i hi j hj
    have hbeq : (⟨(b : G), hDBs hb⟩ : ↥Bs) = b := Subtype.ext rfl
    have h := hIconst (b : G) hb i hi j hj
    rwa [hbeq] at h
  · intro i hi j h
    exact hIfull i hi j fun d hd => h ⟨d, hDBs hd⟩ hd

private theorem class_subset_anchor {G F : Type} [Group G] [Finite G] [Field F] {p n f : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ} {I I₀ : Finset (Fin n)}
    (hFC : GGResNbrFixCentralizesInput) (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (h3n : 3 ≤ n)
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F)
    (hp : p.Prime) (hp2 : p ≠ 2) (hI2 : 2 ≤ I.card)
    (hJI : J = (TableBUE.blockSU (K := F) (n := f) I).map σ)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦)
    (hA₀ : (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I₀)
    (hJK : J ≤ K₀) : I ⊆ I₀ := by
  intro m hm
  by_contra hmI₀
  let bm : ↥Bs := eta.symm (Pi.mulSingle m (Multiplicative.ofAdd (1 : ZMod p)))
  have hbmfix : ∀ φ ∈ ggAutomizer K₀ Bs, φ bm = bm := by
    refine (forall_map_congr_fix_iff eta (ggAutomizer K₀ Bs) bm).mp ?_
    have hv : eta bm = Pi.mulSingle m (Multiplicative.ofAdd (1 : ZMod p)) :=
      MulEquiv.apply_symm_apply eta _
    rw [hv, hA₀]
    exact (forall_bBlockOn_fix_iff hp hp2 I₀ _).mpr fun k hk => by
      have hkm : k ≠ m := fun h => by rw [h] at hk; exact hmI₀ hk
      simp [Pi.mulSingle, hkm]
  obtain ⟨y, hy⟩ := hR.2.2.2.1.2 K₀ hK₀
  have hH : GGResHyp p B Bs x L D J y K₀ :=
    ⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hy, hR.2.1 y K₀ hy, Or.inr hR.2.1⟩
  have hbmK : (bm : G) ∈ Subgroup.centralizer (K₀ : Set G) :=
    hFC G p B Bs x L D J y K₀ hH bm hbmfix
  have hpos : 0 < (I.erase m).card := by rw [Finset.card_erase_of_mem hm]; omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  have hjI : j ∈ I := Finset.mem_of_mem_erase hj
  have hjm : j ≠ m := (Finset.mem_erase.mp hj).1
  have hsub : ({m, j} : Finset (Fin n)) ⊆ I := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht'
    · exact hm
    · rw [Finset.mem_singleton.mp ht']; exact hjI
  have hHK : (TableBUE.blockSU (K := F) (n := f) ({m, j} : Finset (Fin n))).map σ ≤ K₀ := by
    refine (Subgroup.map_mono fun t ht => ?_).trans (hJI.symm ▸ hJK)
    rw [TableBUE.mem_blockSU] at ht ⊢
    exact isBlockOn_finset_mono hsub ht
  exact hLF.not_mem_centralizer_map_blockSU (π := 1) hfield hp h3n
    (i := m) (j := j) (Ne.symm hjm) (Subgroup.centralizer_le hHK hbmK)


private theorem exists_unitary_frame {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B ≠ Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hInn : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ 2 ≤ lab.n)
      p Bs L) :
    ∃ (f : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F n) →* G)
      (χ : Multiplicative (ZMod p) →* Fˣ),
      2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F ∧
        GGSecFiveBPermUniLFrame Bs L eta 1 σ χ := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have h5 : 5 ≤ n := hR.1.1.five_le_of_ne hB eta
  obtain ⟨hcommL, lab, hlab2, hrawlab⟩ := hInn
  obtain ⟨R, hGR, Ilab, Flab, -, -, θ, hPS, hBsN, hind⟩ := largeEvenRawDatum_exists hrawlab
  obtain ⟨hUniL, h2labn⟩ := hPS
  obtain ⟨-, -, hpq⟩ := hUniL
  have hf : 2 ≤ lab.n := h2labn
  have hlab : GGInnerDiagOnLabel
      (fun p lab' => GGSecFiveBPermUniLabel n p lab' ∧ lab'.n = lab.n) p Bs L := by
    refine ⟨hcommL, lab, hlab2, largeEvenRawDatum_mono ?_ hrawlab⟩
    rintro R _ I F ⟨hs, hna, θ, hPS', hBsN', hind'⟩
    exact ⟨hs, hna, θ, ⟨hPS'.1, rfl⟩, hBsN', hind'⟩
  obtain ⟨hpq', F, hFld, hFin, hChar, hN, φ, hFcard, hM, hdiag⟩ :=
    exists_unitary_model_of_uniLabel (n := n) (f := lab.n) hR (by omega) hf hlab
  obtain ⟨-, hBsE, -, -, -⟩ := hR.1.1.tableB_facts
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  obtain ⟨σ, χ, hLF⟩ := exists_uniLFrame_of_model hp hp2 hBsE hBsC
    hR.1.1.card_bstar_inf_centralizer_L.le (by omega) eta hLA hN φ hM hdiag 1
  exact ⟨lab.n, F, hFld, hFin, hChar, σ, χ, hf, hpq, hM.field, hLF⟩

private theorem exists_unitary_frame_two {G : Type} [Group G] [Finite G] {p n : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B ≠ Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hInn : GGInnerDiagOnLabel
      (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n = 1) p Bs L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F n) →* G)
      (χ : Multiplicative (ZMod p) →* Fˣ),
      p ∣ 2 ^ 1 + 1 ∧ CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F ∧
        GGSecFiveBPermUniLFrame Bs L eta 1 σ χ := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  obtain ⟨hpq, F, hFld, hFin, hChar, hN, φ, -, hM, hdiag⟩ :=
    exists_unitary_model_of_uniLabel_of_twoCenter (n := n) (f := 1) hR
      (by have := hR.1.1.five_le_of_ne hB eta; omega)
      (fun _ => hR.1.1.twoCenter_eq_bot_of_B_lt_Bs
        (lt_of_le_of_ne hR.1.1.2.1.1 hB) hR.1.2.2.1.1.le_normalizer) hInn
  obtain ⟨-, hBsE, -, -, -⟩ := hR.1.1.tableB_facts
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  obtain ⟨σ, χ, hLF⟩ := exists_uniLFrame_of_model hp hp2 hBsE hBsC
    hR.1.1.card_bstar_inf_centralizer_L.le
    (by have := hR.1.1.five_le_of_ne hB eta; omega) eta hLA hN φ hM hdiag 1
  exact ⟨F, hFld, hFin, hChar, σ, χ, hpq, hM.field, hLF⟩

theorem GGSecFiveRouteCfg.exists_mem_bCoordinateBlock_of_ne {G : Type} [Group G] [Finite G]
    {p n : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hTBF : GGTBFixInput) (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hLB : GGLBalanceInput) (hRoot : GGSecFiveBProperRootInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B ≠ Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hInn : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ 2 ≤ lab.n) p Bs L) :
    ∃ K ∈ 𝒦, ∃ i0 : Fin n,
      (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  obtain ⟨f, F, hFld, hFin, hChar, σ, χ, hf, hpq, hfield, hLF⟩ :=
    exists_unitary_frame hR hB eta hLA hInn
  have hDB : D ≤ B := hR.1.1.2.2.1.1
  have hDBs : D ≤ Bs := hDB.trans hR.1.1.2.1.1
  obtain ⟨I, hI2, hJI, hconst, hpair, hpJ⟩ :=
    exists_class_data hLF hfield hf hp hp2 hpq hDBs
      hR.1.1.2.2.1.2.2.2.2.2.1 hR.1.1.2.2.1.2.2.2.2.1
  obtain ⟨a, a', haa', hroot⟩ := hRoot G p B Bs x L D J 𝒦 hR hB n eta hEta hLA
  have hDBa : ∀ b : ↥Bs, (b : G) ∈ D → eta b a = eta b a' := fun b hb => (hroot b).mp (hDB hb)
  have haI : a ∈ I := (hpair a a' haa' hDBa).1
  have ha'I : a' ∈ I := (hpair a a' haa' hDBa).2
  obtain ⟨k, hIerase⟩ := class_erase (D := D) hp hR.1.1.2.2.1.2.2.1
    (class_card hLF hDBs hR.1.1.2.2.1.2.2.2.2.2.2 hJI hconst haI ha'I hroot)
  obtain ⟨K₀, hK₀, I₀, y₀b, hI₀ne, hy₀B, hA₀, hy₀fix, hy₀ne, hJK⟩ :=
    anchor_data hTBF hX hTCJ hRig hTPn hA8 hraw hiso hFC hLB hR hB eta hEta hLA hp hp2 hpJ
  have h5 : 5 ≤ n := hR.1.1.five_le_of_ne hB eta
  have hII₀ : I ⊆ I₀ :=
    class_subset_anchor hFC hR eta (by omega) hLF hfield hp hp2 hI2 hJI hK₀ hA₀ hJK
  have hI₀ne' : I₀ ≠ Finset.univ := by
    intro h
    have h1 : eta y₀b = 1 := funext fun k => hy₀fix k (h ▸ Finset.mem_univ k)
    exact hy₀ne (eta.injective (by simpa using h1))
  refine ⟨K₀, hK₀, k, ?_⟩
  have hI₀erase : I₀ = Finset.univ.erase k := by
    have hsub : Finset.univ.erase k ⊆ I₀ := hIerase ▸ hII₀
    have hcardK : (Finset.univ.erase k).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    have hle : I₀.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ I₀
    have hne : I₀.card ≠ n := by
      intro h
      exact hI₀ne' (Finset.eq_univ_of_card I₀ (by rwa [Fintype.card_fin]))
    have hcf : (Finset.univ.erase k).card ≤ I₀.card := Finset.card_le_card hsub
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  rw [hA₀, hI₀erase, bBlockOn_univ_erase]

theorem GGSecFiveRouteCfg.exists_qTwo_line_of_ne {G : Type} [Group G] [Finite G]
    {p n : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hTBF : GGTBFixInput) (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hLB : GGLBalanceInput) (hRoot : GGSecFiveBProperRootInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B ≠ Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hInn : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n = 1) p Bs L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F n) →* G)
      (χ : Multiplicative (ZMod p) →* Fˣ),
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F ∧
        GGSecFiveBPermUniLFrame Bs L eta 1 σ χ ∧
        ((∃ k : Fin n, J = (TableBUE.blockSU (K := F) (n := 1) (Finset.univ.erase k)).map σ ∧
            ∃ K ∈ 𝒦, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
              bCoordinateBlock n p k) ∨
          ∃ a a' : Fin n, a ≠ a' ∧ (∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a')) ∧
            4 ≤ (({a, a'} : Finset (Fin n))ᶜ).card ∧
            J = (TableBUE.blockSU (K := F) (n := 1) ({a, a'} : Finset (Fin n))ᶜ).map σ ∧
            ∃ K ∈ 𝒦, J ≤ K ∧ (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
              bBlockOn n p ({a, a'} : Finset (Fin n))ᶜ) := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  obtain ⟨F, hFld, hFin, hChar, σ, χ, hpq, hfield, hLF⟩ :=
    exists_unitary_frame_two hR hB eta hLA hInn
  have hDB : D ≤ B := hR.1.1.2.2.1.1
  have hDBs : D ≤ Bs := hDB.trans hR.1.1.2.1.1
  have hJeq : D = B ⊓ Subgroup.centralizer (J : Set G) := hR.1.1.2.2.1.2.2.2.2.2.2
  obtain ⟨I, hI4, hJI, hconst, hIfull, hpJ⟩ :=
    exists_class_data_two hLF hfield hp hp2 hpq hDBs
      hR.1.1.2.2.1.2.2.2.2.2.1 hR.1.1.2.2.1.2.2.2.2.1
  obtain ⟨a, a', haa', hroot⟩ := hRoot G p B Bs x L D J 𝒦 hR hB n eta hEta hLA
  obtain ⟨K₀, hK₀, I₀, y₀b, hI₀ne, hy₀B, hA₀, hy₀fix, hy₀ne, hJK⟩ :=
    anchor_data hTBF hX hTCJ hRig hTPn hA8 hraw hiso hFC hLB hR hB eta hEta hLA hp hp2 hpJ
  have hII₀ : I ⊆ I₀ :=
    class_subset_anchor hFC hR eta (by have := hR.1.1.five_le_of_ne hB eta; omega) hLF hfield
      hp hp2 (by omega) hJI hK₀ hA₀ hJK
  refine ⟨F, hFld, hFin, hChar, σ, χ, hfield, hLF, ?_⟩
  by_cases haI : a ∈ I
  · have ha'I : a' ∈ I := hIfull a haI a' fun b hb => ((hroot b).mp (hDB hb)).symm
    obtain ⟨k, hIerase⟩ := class_erase (D := D) hp hR.1.1.2.2.1.2.2.1
      (class_card hLF hDBs hJeq hJI hconst haI ha'I hroot)
    refine Or.inl ⟨k, ?_, K₀, hK₀, ?_⟩
    · rw [hJI, hIerase]
    · rw [hA₀, anchor_eq_univ_erase (hIerase ▸ hII₀) hy₀fix hy₀ne, bBlockOn_univ_erase]
  · have hIcompl : I = ({a, a'} : Finset (Fin n))ᶜ :=
      eq_compl_pair_of_two hLF hDB hJeq hJI hconst hIfull hroot hp
        hR.1.1.2.2.1.2.2.1 hI4 haI
    have ha₀ : a ∉ I₀ := fun ha =>
      hy₀ne (anchor_eq_one hIcompl hII₀ hroot hy₀B hy₀fix (Or.inl ha))
    have ha'₀ : a' ∉ I₀ := fun ha =>
      hy₀ne (anchor_eq_one hIcompl hII₀ hroot hy₀B hy₀fix (Or.inr ha))
    have hI₀sub : I₀ ⊆ I := by
      rw [hIcompl]
      intro j hj
      rw [Finset.mem_compl]
      intro hmem
      rw [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact ha₀ (h ▸ hj)
      · exact ha'₀ (h ▸ hj)
    have hI₀eq : I₀ = I := le_antisymm hI₀sub hII₀
    refine Or.inr ⟨a, a', haa', hroot, hIcompl ▸ hI4, ?_, K₀, hK₀, hJK, ?_⟩
    · rw [hJI, hIcompl]
    · rw [hA₀, hI₀eq, hIcompl]

end CFSG.StandardType

end
