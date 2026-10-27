module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofU42
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Four
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3Inner
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofExcInner
import CFSG.RankThree.PartTwo.Sec21.Item223KFactsProofCore
import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofModels
import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Lie2Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut map_bar_comm)
open CFSG.RankThree.PartOne.KFU (torusSU torusVec diagU diagU_val mem_torusSU_iff diagU_apply_same)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Matrix

theorem le_inSubgroup_pCore_of_normal' {G : Type*} [Group G] {p : ℕ} {Y T : Subgroup G}
    (hTY : T ≤ Y) (hTn : (T.subgroupOf Y).Normal) (hT : IsPGroup p T) :
    T ≤ CFSG.inSubgroup (CFSG.pCore p) Y := by
  have hle : T.subgroupOf Y ≤ CFSG.pCore p Y :=
    le_sSup ⟨hTn, hT.comap_of_injective Y.subtype Y.subtype_injective⟩
  have h := Subgroup.map_mono (f := Y.subtype) hle
  rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hTY] at h

theorem conj_injective' {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot, ← Subgroup.mem_bot, ← hZ, Subgroup.mem_center_iff]
  intro y
  have h1 := congrArg (fun φ : MulAut X => φ y) hx
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc y * x = x * y * x⁻¹ * x := by rw [h1]
    _ = x * y := by group

theorem mul_conj_mul_inv' {X : Type*} [Group X] (τ : MulAut X) (x : X) :
    τ * MulAut.conj x * τ⁻¹ = MulAut.conj (τ x) := by
  ext m
  simp [MulAut.mul_apply, map_mul, map_inv]

section Matrix

variable {K : Type} [Field K]

theorem card_le_of_two_ne_zero [Finite K] (h2 : (2 : K) = 0)
    (hcube : ∀ x : K, x ≠ 0 → x ^ 3 = 1) {u : GL (Fin 4) K}
    (hun : ∀ j, ∑ i,
      (u : Matrix (Fin 4) (Fin 4) K) i j ^ 2 * (u : Matrix (Fin 4) (Fin 4) K) i j = 1)
    (D : Subgroup (GL (Fin 4) K))
    (hD : ∀ g ∈ D, ∃ d : Fin 4 → Kˣ, ∏ i, d i = 1 ∧ diagU d = g)
    (hDu : ∀ g ∈ D, u * g = g * u) {i i' j : Fin 4} (hii' : i ≠ i')
    (hi : (u : Matrix (Fin 4) (Fin 4) K) i j ≠ 0) (hi' : (u : Matrix (Fin 4) (Fin 4) K) i' j ≠ 0) :
    Nat.card D ≤ Nat.card Kˣ := by
  classical
  obtain ⟨m, -, hother⟩ := exists_zero_of_two_ne_zero h2 hcube
    (c := fun x => (u : Matrix (Fin 4) (Fin 4) K) x j) (hun j) hii' hi hi'
  have hent : ∀ g ∈ D, ∀ d : Fin 4 → Kˣ, diagU d = g → ∀ x, x ≠ m → d x = d j := by
    intro g hg d hd x hx
    by_contra hne
    have hc : u * diagU d = diagU d * u := by rw [hd]; exact hDu g hg
    exact hother x hx (Item223KFactsProof.entry_eq_zero_of_commute_diagU hc hne)
  have hval : ∀ g ∈ D, ∀ d : Fin 4 → Kˣ, diagU d = g →
      ((g : Matrix (Fin 4) (Fin 4) K) j j) = (d j : K) := by
    intro g _ d hd
    rw [← hd, diagU_apply_same]
  let f : D → Kˣ := fun g => (hD g g.2).choose j
  have hf : Function.Injective f := by
    intro g g' hgg'
    obtain ⟨hp, hd⟩ := (hD g g.2).choose_spec
    obtain ⟨hp', hd'⟩ := (hD g' g'.2).choose_spec
    set d := (hD g g.2).choose
    set d' := (hD g' g'.2).choose
    have hj : d j = d' j := hgg'
    have hoff : ∀ x, x ≠ m → d x = d' x := fun x hx => by
      rw [hent g g.2 d hd x hx, hent g' g'.2 d' hd' x hx, hj]
    have hm : d m = d' m := by
      have e1 := Finset.mul_prod_erase Finset.univ d (Finset.mem_univ m)
      have e2 := Finset.mul_prod_erase Finset.univ d' (Finset.mem_univ m)
      rw [hp] at e1
      rw [hp'] at e2
      have hpe : ∏ x ∈ Finset.univ.erase m, d x = ∏ x ∈ Finset.univ.erase m, d' x :=
        Finset.prod_congr rfl fun x hx => hoff x (Finset.ne_of_mem_erase hx)
      rw [hpe] at e1
      exact mul_right_cancel (e1.trans e2.symm)
    have hdd : d = d' := funext fun x => by
      rcases eq_or_ne x m with rfl | hx
      · exact hm
      · exact hoff x hx
    apply Subtype.ext
    rw [← hd, ← hd', hdd]
  exact Nat.card_le_card_of_injective f hf

theorem isDiag_conj_of_col (u v : Matrix (Fin 4) (Fin 4) K) (hv : ∀ j k, v j k = u k j ^ 2)
    (hcol : ∀ j i i', u i j ≠ 0 → u i' j ≠ 0 → i = i') (δ : Fin 4 → K) :
    (u * Matrix.diagonal δ * v).IsDiag := by
  intro i k hik
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.mul_diagonal, hv]
  by_contra hne
  have h1 : u i j ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have h2 : u k j ≠ 0 := fun h => hne (by rw [h, zero_pow two_ne_zero, mul_zero])
  exact hik (hcol j i k h1 h2)

end Matrix

end Item211Lie2Proof

open Item211Lie2Proof
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut map_bar_comm)
open CFSG.RankThree.PartOne.KFU (torusSU torusVec diagU diagU_val mem_torusSU_iff diagU_apply_same)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (restrictAutHom)
open scoped Matrix

theorem ks211U42CharThree_holds : KS211U42CharThree := by
  intro X _ _ ⟨e⟩ D hDinn hDe hD9 τ ⟨k, hk⟩ hτD hτR
  classical
  set K := GaloisField 2 (2 * 1) with hKdef
  have hU : UnitaryFieldData 2 1 K := Item223KFactsProof.unitaryFieldData_galoisField le_rfl
  have hfin : Finite K := hU.finite
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, hU.card]
    norm_num
  have : CharP K 2 := hU.charP
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hcube : ∀ x : K, x ≠ 0 → x ^ 3 = 1 := fun x hx => by
    have := FiniteField.pow_card_sub_one_eq_one x hx
    rwa [hcardK] at this
  have hbar : ∀ c : K, hU.bar c = c ^ 2 := fun c => by rw [hU.bar_apply, pow_one]
  have hunits : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hcardK]
  have : Finite (Matrix.ProjGenLinGroup (Fin 4) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (projSU 4 2 1) := Subtype.finite
  have hZY : Subgroup.center (projSU 4 2 1) = ⊥ :=
    Item21Early2Proof.center_projSU_four_eq_bot le_rfl
  have hZX : Subgroup.center X = ⊥ := center_eq_bot_of_mulEquiv e hZY
  have hinjX := conj_injective' hZX
  set S := unitarySU 2 1 K 4 with hSdef
  set D₀ := D.comap (MulAut.conj : X →* MulAut X) with hD₀
  have hD₀e : IsElemAbelian 3 D₀ :=
    Item211LieProof.isElemAbelian_comap_of_injective hinjX hDe
  have hD₀9 : Nat.card D₀ = 9 := by
    rw [Item211LieProof.card_comap_conj hZX hDinn, hD9]
  set E := D₀.map e.toMonoidHom with hE
  have hEe : ∀ x ∈ E, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hD₀e.2 x hx, map_one]
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    have h0 : x * y = y * x := congrArg Subtype.val (hD₀e.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [← map_mul, ← map_mul, h0]
  obtain ⟨ψ, hψ⟩ := Item223KFactsProof.exists_diag_model_le (k := 1) le_rfl odd_one
    (MulEquiv.refl _) hZY E hEe hEc
  set θ : S ≃* X := ψ.trans e.symm with hθ
  have hθD : ∀ g : S, θ g ∈ D₀ → (g : GL (Fin 4) K) ∈ torusSU 3 4 K := by
    intro g hg
    refine hψ g ⟨θ g, hg, ?_⟩
    simp [hθ]
  have hZS : Subgroup.center S = ⊥ := center_eq_bot_of_mulEquiv θ hZX
  have hinjS := conj_injective' hZS
  have hmemU : ∀ g : S, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 ∧
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map hU.bar)ᵀ *
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 :=
    fun g => (mem_unitarySU_iff hU).mp g.2
  have hnorm : ∀ (g : S) (j : Fin 4), ∑ i, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j ^ 2 *
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j = 1 := by
    intro g j
    have := congrFun (congrFun (hmemU g).2 j) j
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    simpa only [Matrix.transpose_apply, Matrix.map_apply, hbar] using this
  have hinv : ∀ g : S, (((g : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map hU.bar)ᵀ :=
    fun g => Units.inv_eq_of_mul_eq_one_left (hmemU g).2
  have htorS : torusSU 3 4 K ≤ S :=
    CFSG.RankThree.PartOne.KFU.torusSU_le_unitarySU hU (by norm_num)
  have hdiagT : ∀ g : S, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag →
      (g : GL (Fin 4) K) ∈ torusSU 3 4 K := by
    intro g hg
    obtain ⟨d, hd⟩ := CFSG.RankThree.PartOne.KFU.exists_diagU_of_isDiag hg
    refine mem_torusSU_iff.mpr ⟨d, fun i => Units.ext ?_, ?_, hd⟩
    · rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact hcube _ (d i).ne_zero
    · apply Units.ext
      have h1 := (hmemU g).1
      rw [← hd, CFSG.RankThree.PartOne.KFU.det_diagU] at h1
      rw [Units.coe_prod, h1, Units.val_one]
  set Tor : Subgroup S := (torusSU 3 4 K).comap S.subtype with hTor
  set DS : Subgroup S := D₀.comap θ.toMonoidHom with hDS
  have hDS9 : Nat.card DS = 9 := by
    rw [hDS, ← hD₀9]
    exact Nat.card_congr ((θ.toEquiv.subtypeEquiv fun _ => Iff.rfl))
  have hnormal : ∀ u : S, (∀ g ∈ DS, u * g = g * u) → ∀ t ∈ Tor, u * t * u⁻¹ ∈ Tor := by
    intro u hu t ht
    have hcol : ∀ j i i', ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j ≠ 0 →
        ((u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i' j ≠ 0 → i = i' := by
      intro j i i' hi hi'
      by_contra hii'
      have hle := card_le_of_two_ne_zero h2 hcube (u := (u : GL (Fin 4) K)) (hnorm u)
        (DS.map S.subtype) (by
          rintro _ ⟨g, hg, rfl⟩
          obtain ⟨d, -, hd1, hd⟩ := mem_torusSU_iff.mp (hθD g hg)
          exact ⟨d, hd1, hd⟩)
        (by
          rintro _ ⟨g, hg, rfl⟩
          exact congrArg Subtype.val (hu g hg)) hii' hi hi'
      rw [Subgroup.card_map_of_injective S.subtype_injective, hDS9, hunits] at hle
      omega
    have ht' : (t : GL (Fin 4) K) ∈ torusSU 3 4 K := ht
    obtain ⟨δ, -, -, hδ⟩ := mem_torusSU_iff.mp ht'
    show ((u * t * u⁻¹ : S) : GL (Fin 4) K) ∈ torusSU 3 4 K
    apply hdiagT
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
      hinv u, ← hδ, diagU_val]
    exact isDiag_conj_of_col _ _ (fun j k => by
      rw [Matrix.transpose_apply, Matrix.map_apply, hbar]) hcol _
  set Y := (MulAut.conj : X →* MulAut X).range ⊓ Subgroup.centralizer (D : Set (MulAut X))
    with hY
  set P : Subgroup (MulAut X) := Tor.map ((MulAut.conj : X →* MulAut X).comp θ.toMonoidHom)
    with hP
  have hTorComm : ∀ g ∈ Tor, ∀ g' : S, (g' : GL (Fin 4) K) ∈ torusSU 3 4 K → g * g' = g' * g := by
    intro g hg g' hg'
    have hg0 : (g : GL (Fin 4) K) ∈ torusSU 3 4 K := hg
    obtain ⟨d, -, -, hd⟩ := mem_torusSU_iff.mp hg0
    obtain ⟨d', -, -, hd'⟩ := mem_torusSU_iff.mp hg'
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hd, ← hd', CFSG.RankThree.PartOne.KFU.diagU_mul,
      CFSG.RankThree.PartOne.KFU.diagU_mul, mul_comm d d']
  have hPY : P ≤ Y := by
    rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨θ g, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun δ hδ => ?_⟩
    obtain ⟨x, rfl⟩ := hDinn hδ
    have hxD : x ∈ D₀ := hδ
    have hx' : (θ.symm x : GL (Fin 4) K) ∈ torusSU 3 4 K :=
      hθD _ (by rw [MulEquiv.apply_symm_apply]; exact hxD)
    have hc := hTorComm g hg _ hx'
    have hc' : θ g * x = x * θ g := by
      have := congrArg θ hc
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [← map_mul, ← map_mul, hc']
  have hP3 : IsPGroup 3 P := by
    rintro ⟨_, ⟨g, hg, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hg0 : (g : GL (Fin 4) K) ∈ torusSU 3 4 K := hg
    obtain ⟨d, hd3, -, hd⟩ := mem_torusSU_iff.mp hg0
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hd, CFSG.RankThree.PartOne.KFU.diagU_pow]
      have : d ^ 3 = 1 := funext hd3
      rw [this, CFSG.RankThree.PartOne.KFU.diagU_one]
    simp only [pow_one, Subgroup.coe_pow, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, OneMemClass.coe_one]
    rw [← map_pow, ← map_pow, hg3, map_one, map_one]
  have hPn : (P.subgroupOf Y).Normal := by
    refine ⟨fun p hp y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hp ⊢
    obtain ⟨g, hg, hpg⟩ := hp
    obtain ⟨z, hz⟩ := (Subgroup.mem_inf.mp y.2).1
    have hzC : ∀ x ∈ D₀, z * x = x * z := by
      intro x hx
      have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp y.2).2 _ hx
      rw [← hz, ← map_mul, ← map_mul] at h1
      exact (hinjX h1).symm
    have hu : ∀ g' ∈ DS, θ.symm z * g' = g' * θ.symm z := by
      intro g' hg'
      apply θ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hzC _ hg'
    refine ⟨θ.symm z * g * (θ.symm z)⁻¹, hnormal _ hu g hg, ?_⟩
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply] at hpg ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hz, ← hpg, map_mul, map_mul,
      map_inv, MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hPR := le_inSubgroup_pCore_of_normal' hPY hPn hP3
  have hfix : ∀ g ∈ Tor, τ (θ g) = θ g := by
    intro g hg
    have h1 := Subgroup.mem_centralizer_iff.mp hτR _ (hPR ⟨g, hg, rfl⟩)
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply] at h1
    apply hinjX
    rw [← mul_conj_mul_inv', ← h1, mul_inv_cancel_right]
  set τS : MulAut S := MulAut.congr θ.symm τ with hτS
  have hτSfix : ∀ g ∈ Tor, τS g = g := by
    intro g hg
    show θ.symm (τ (θ g)) = g
    rw [hfix g hg, MulEquiv.symm_apply_apply]
  have hτSk : τS ^ (2 ^ k) = 1 := by rw [hτS, ← map_pow, hk, map_one]
  have hT : StatedClassicalModel S .PSU 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩,
      GaloisField 2 (2 * 1), inferInstance, inferInstance, by rw [hU.card]; norm_num,
      ⟨ψ.trans (Sec4.projSUEquivStatedProj 4 2 1)⟩⟩
  obtain ⟨-, -, hout, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound S 4 2 1 hT
  have hindex : (CFSG.ComponentClassification.OuterAutomorphisms.inner S).index = 2 := by
    rw [Subgroup.index, hout]
    norm_num
  obtain ⟨ω, hω1⟩ : ∃ ω : Kˣ, ω ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card Kˣ ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun a b => (h a).trans (h b).symm⟩
    omega
  have hω3 : ω ^ 3 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hcube _ ω.ne_zero)
  have hωK : (ω : K) ≠ (ω : K) ^ 2 := by
    intro h
    apply hω1
    apply Units.ext
    have h1 : (ω : K) * ((ω : K) - 1) = 0 := by
      rw [mul_sub, mul_one (ω : K), ← sq (ω : K), ← h, sub_self]
    rcases mul_eq_zero.mp h1 with h3 | h3
    · exact absurd h3 ω.ne_zero
    · rw [Units.val_one]
      exact sub_eq_zero.mp h3
  set dv : Fin 4 → Kˣ := ![ω, ω, ω, 1] with hdv
  have ht₀T : (diagU dv : GL (Fin 4) K) ∈ torusSU 3 4 K := by
    refine mem_torusSU_iff.mpr ⟨dv, fun i => ?_, ?_, rfl⟩
    · fin_cases i <;> simp [hdv, hω3]
    · simp [hdv, Fin.prod_univ_four, ← pow_three', hω3]
  set t₀ : S := ⟨diagU dv, htorS ht₀T⟩ with ht₀
  have ht₀Tor : t₀ ∈ Tor := ht₀T
  set σ : K ≃+* K := frobeniusEquiv K 2 with hσ
  have hσx : ∀ x : K, σ x = x ^ 2 := fun x => frobeniusEquiv_apply K 2 x
  set φS : MulAut S := (restrictAutHom (glAut (ι := Fin 4) (K := K)) S
    fun σ' g hg => by
      obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff hU).mp hg
      refine (mem_unitarySU_iff hU).mpr ⟨?_, ?_⟩
      · rw [coe_glAut, ← RingEquiv.mapMatrix_apply, ← RingEquiv.map_det, hdet, map_one]
      · rw [coe_glAut]
        have hcomm : ((g : Matrix (Fin 4) (Fin 4) K).map σ').map hU.bar =
            ((g : Matrix (Fin 4) (Fin 4) K).map hU.bar).map σ' := by
          ext i j
          simp only [Matrix.map_apply]
          exact (map_bar_comm hU σ' _).symm
        rw [hcomm, ← Matrix.transpose_map]
        have := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map σ') hu
        rw [Matrix.map_mul, Matrix.map_one _ (map_zero σ') (map_one σ')] at this
        exact this) σ with hφS
  have hφSval : ∀ g : S, ((φS g : S) : GL (Fin 4) K) = glAut σ g := fun g => rfl
  have ht₀m : ((t₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal ![(ω : K), (ω : K), (ω : K), 1] := by
    rw [ht₀]
    change ((diagU dv : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _
    rw [diagU_val]
    congr 1
    funext i
    fin_cases i <;> simp [hdv]
  have hφt₀m : (((φS t₀ : S) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal ![(ω : K) ^ 2, (ω : K) ^ 2, (ω : K) ^ 2, 1] := by
    rw [hφSval, coe_glAut, ht₀m, Matrix.diagonal_map (map_zero σ)]
    congr 1
    funext i
    fin_cases i <;> simp [hσx]
  have htrace : ∀ g : S, g * t₀ * g⁻¹ ≠ φS t₀ := by
    intro g hg
    have h1 := congrArg (fun x : S => Matrix.trace ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
      hg
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have htr : ∀ a b c d : K, Matrix.trace (Matrix.diagonal ![a, b, c, d]) = a + b + c + d := by
      intro a b c d
      rw [Matrix.trace_diagonal, Fin.sum_univ_four]
      rfl
    rw [Units.val_mul, Units.val_mul, Matrix.trace_units_conj, ht₀m, hφt₀m, htr, htr] at h1
    have h3 : (ω : K) + (ω : K) + (ω : K) + 1 = (ω : K) + 1 := by
      rw [show (ω : K) + (ω : K) = 2 * (ω : K) by ring, h2, zero_mul, zero_add]
    have h4 : (ω : K) ^ 2 + (ω : K) ^ 2 + (ω : K) ^ 2 + 1 = (ω : K) ^ 2 + 1 := by
      rw [show (ω : K) ^ 2 + (ω : K) ^ 2 = 2 * (ω : K) ^ 2 by ring, h2, zero_mul, zero_add]
    rw [h3, h4] at h1
    exact hωK (add_right_cancel h1)
  have hφout : φS ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
    rintro ⟨g, hg⟩
    apply htrace g
    have := congrArg (fun α : MulAut S => α t₀) hg
    simp only [MulAut.conj_apply] at this
    exact this
  have hτS1 : τS = 1 := by
    by_cases hin : τS ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner S
    · obtain ⟨g, hg⟩ := hin
      have hgT : ∀ t ∈ Tor, g * t = t * g := by
        intro t ht
        have := congrArg (fun α : MulAut S => α t) hg
        simp only [MulAut.conj_apply] at this
        rw [hτSfix t ht] at this
        calc g * t = g * t * g⁻¹ * g := by group
          _ = t * g := by rw [this]
      have hgdiag : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag := by
        intro i j hij
        have hω2 : ω ^ 2 ≠ 1 := by
          intro h
          apply hω1
          calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
            _ = 1 := by rw [hω3, h, inv_one, one_mul]
        obtain ⟨t, htT, htij⟩ := CFSG.RankThree.PartOne.KFU.torusSU_char_distinct (n := 4)
          (K := K) hω3 hω2 hij
        obtain ⟨d, -, -, hd⟩ := mem_torusSU_iff.mp htT
        have hc : (g : GL (Fin 4) K) * diagU d = diagU d * (g : GL (Fin 4) K) := by
          rw [hd]
          exact congrArg Subtype.val (hgT ⟨t, htorS htT⟩ htT)
        rw [← hd, diagU_apply_same, diagU_apply_same] at htij
        exact Item223KFactsProof.entry_eq_zero_of_commute_diagU hc
          (fun h => htij (congrArg Units.val h))
      have hgTor := hdiagT g hgdiag
      obtain ⟨d, hd3, -, hd⟩ := mem_torusSU_iff.mp hgTor
      have hg3 : g ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← hd, CFSG.RankThree.PartOne.KFU.diagU_pow]
        have : d ^ 3 = 1 := funext hd3
        rw [this, CFSG.RankThree.PartOne.KFU.diagU_one]
      have hτ3 : τS ^ 3 = 1 := by rw [← hg, ← map_pow, hg3, map_one]
      have := mem_of_pow_three_mem (⊥ : Subgroup (MulAut S)) (by rw [hτ3]; exact Subgroup.one_mem _)
        (by rw [hτSk]; exact Subgroup.one_mem _)
      exact Subgroup.mem_bot.mp this
    · exfalso
      have hmem : φS⁻¹ * τS ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
        rw [Subgroup.mul_mem_iff_of_index_two hindex]
        exact ⟨fun h => absurd (inv_inv φS ▸
            (CFSG.ComponentClassification.OuterAutomorphisms.inner S).inv_mem h) hφout,
          fun h => absurd h hin⟩
      obtain ⟨g, hg⟩ := hmem
      have hτeq : τS = φS * MulAut.conj g := by rw [hg, mul_inv_cancel_left]
      have h1 := hτSfix t₀ ht₀Tor
      rw [hτeq, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
      apply htrace (φS g)⁻¹
      calc (φS g)⁻¹ * t₀ * (φS g)⁻¹⁻¹ = (φS g)⁻¹ * (φS g * φS t₀ * (φS g)⁻¹) * (φS g) := by
            rw [h1, inv_inv]
        _ = φS t₀ := by group
  rw [hτS] at hτS1
  have := congrArg (MulAut.congr θ.symm).symm hτS1
  rwa [MulEquiv.symm_apply_apply, map_one] at this

end CFSG.RankThree.PartTwo.Sec21
