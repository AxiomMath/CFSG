module

public import CFSG.Quasithin.SteinbergCFPlaneSupportGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathSolvable
public import CFSG.GH74.M12.HypGroup
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.SteinbergCF

open Module CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.Quasithin.B6
open scoped commutatorElement

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem sup_eq_planeSupport {r : ℕ} {I : Fin r → Submodule k V} {V₀ : Submodule k V}
    (hI : iSupIndep I) (hc : IsCompl (⨆ j, I j) V₀) {i : Fin r} {L A : Subgroup (V ≃ₗ[k] V)}
    (hLS : L ≤ planeSupport I V₀ i)
    (hAI : ∀ a ∈ A, (I i).map (a : V →ₗ[k] V) = I i)
    (hAV₀ : ∀ a ∈ A, ∀ v ∈ V₀, a v ∈ V₀)
    (hAperm : ∀ a ∈ A, ∀ j, ∃ j', (I j).map (a : V →ₗ[k] V) = I j')
    (hsum : I i ⊔ fixGL A = ⊤)
    (hW : QuasithinUnique.Setup.Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) (I i))
    (hsurj : Function.Surjective (resSub (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) (I i) hW)) :
    L ⊔ A = planeSupport I V₀ i := by
  have hspan : (⨆ j, I j) ⊔ V₀ = ⊤ := codisjoint_iff.mp hc.2
  have hdisp : ∀ a ∈ A, ∀ v, a v - v ∈ I i := by
    intro a ha v
    have hv : v ∈ I i ⊔ fixGL A := hsum ▸ Submodule.mem_top
    obtain ⟨x, hx, c, hc', rfl⟩ := Submodule.mem_sup.mp hv
    have hax : a x ∈ I i := apply_mem_of_mem_submoduleStab (U := I i) (hAI a ha) hx
    have hca : a c = c := hc' a ha
    rw [map_add, hca, show a x + c - (x + c) = a x - x by abel]
    exact (I i).sub_mem hax hx
  have hAS : A ≤ planeSupport I V₀ i := by
    intro a ha
    refine ⟨hAI a ha, fun v hv => ?_, fun j hj w hw => ?_⟩
    · have h1 : a v - v ∈ V₀ := V₀.sub_mem (hAV₀ a ha v hv) hv
      have h2 : a v - v ∈ ⨆ l, I l := le_iSup I i (hdisp a ha v)
      exact sub_eq_zero.mp ((Submodule.disjoint_def.mp hc.1) _ h2 h1)
    · obtain ⟨j', hj'⟩ := hAperm a ha j
      have haw : a w ∈ I j' := hj' ▸ ⟨w, hw, rfl⟩
      have hd := hdisp a ha w
      by_cases h1 : j' = j
      · subst h1
        exact sub_eq_zero.mp ((Submodule.disjoint_def.mp (hI.pairwiseDisjoint hj))
          _ ((I j').sub_mem haw hw) hd)
      · by_cases h2 : j' = i
        · subst h2
          have hwi : w ∈ I j' := by
            have := (I j').sub_mem haw hd
            rwa [sub_sub_cancel] at this
          have hw0 : w = 0 := (Submodule.disjoint_def.mp (hI.pairwiseDisjoint hj)) w hw hwi
          rw [hw0, map_zero]
        · have hsum' : a w ∈ ⨆ (l) (_ : l ≠ j'), I l := by
            have e : a w = w + (a w - w) := by abel
            rw [e]
            exact Submodule.add_mem _ (le_iSup₂_of_le (f := fun l (_ : l ≠ j') => I l) j
              (Ne.symm h1) le_rfl hw) (le_iSup₂_of_le (f := fun l (_ : l ≠ j') => I l) i
              (Ne.symm h2) le_rfl hd)
          have ha0 : a w = 0 := (Submodule.disjoint_def.mp (hI j')) _ haw hsum'
          have hw0 : w = 0 := by
            have := congrArg (fun u => a.symm u) ha0
            simpa using this
          rw [ha0, hw0]
  have hle : L ⊔ A ≤ planeSupport I V₀ i := sup_le hLS hAS
  refine le_antisymm hle fun s hs => ?_
  obtain ⟨t, ht⟩ := hsurj (s.ofSubmodules (I i) (I i) hs.1)
  have hts : ∀ v ∈ I i, (t : V ≃ₗ[k] V) v = s v := by
    intro v hv
    have := congrArg (fun f : I i ≃ₗ[k] I i => ((f ⟨v, hv⟩ : I i) : V)) ht
    simpa [resSub_apply] using this
  have hmem : (t : V ≃ₗ[k] V)⁻¹ * s ∈ planeSupport I V₀ i := mul_mem (inv_mem (hle t.2)) hs
  have h1 := eq_one_of_mem_planeSupport hspan hmem fun v hv => by
    rw [LinearEquiv.mul_apply, ← hts v hv]
    exact gl_inv_apply _ _
  rw [inv_mul_eq_one] at h1
  rw [← h1]
  exact t.2

theorem eq_coordProduct_of_mem [CharP k 2] [FiniteDimensional k V] [Finite V] {r : ℕ}
    {I : Fin r → Submodule k V} {V₀ : Submodule k V} (hI : iSupIndep I)
    (hc : IsCompl (⨆ j, I j) V₀) (hdim : ∀ i, finrank k (I i) = 2) (hk : Nat.card k = 2)
    (hcent : ∀ i, ∀ a ∈ planeSupport I V₀ i, a ≠ 1 → a * a = 1 →
      ∀ s ∈ planeSupport I V₀ i, s * a = a * s → s = 1 ∨ s = a)
    (hext : ∀ i (e : V ≃ₗ[k] V), (I i).map (e : V →ₗ[k] V) = I i →
      ∃ s ∈ planeSupport I V₀ i, ∀ v ∈ I i, s v = e v)
    (Ω : Set (Subgroup (V ≃ₗ[k] V)))
    (hΩ : ∀ E ∈ Ω, IsElementaryAbelian 2 E ∧ E ≠ ⊥ ∧
      Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) E)
    (hΩsub : ∀ E ∈ Ω, ∀ E₀ ≤ E, E₀ ≠ ⊥ →
      Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) E₀ → E₀ ∈ Ω)
    (hΩA : ∀ E ∈ Ω, ∃ i, ∃ A ≤ E, A ≤ planeSupport I V₀ i ∧ Nat.card A = 2 ∧
      ∀ e ∈ E, (I i).map (e : V →ₗ[k] V) = I i) :
    ∀ E ∈ Ω, ∃ J : Finset (Fin r), J.Nonempty ∧ ∃ a : Fin r → Subgroup (V ≃ₗ[k] V),
      (∀ i ∈ J, a i ≤ planeSupport I V₀ i ∧ Nat.card (a i) = 2) ∧ E = ⨆ i ∈ J, a i := by
  classical
  have hspan : (⨆ j, I j) ⊔ V₀ = ⊤ := codisjoint_iff.mp hc.2
  have : Finite (V ≃ₗ[k] V) :=
    Finite.of_injective (fun f : V ≃ₗ[k] V => (f : V → V)) DFunLike.coe_injective
  suffices key : ∀ n, ∀ E ∈ Ω, Nat.card E = n → ∃ J : Finset (Fin r), J.Nonempty ∧
      ∃ a : Fin r → Subgroup (V ≃ₗ[k] V),
        (∀ i ∈ J, a i ≤ planeSupport I V₀ i ∧ Nat.card (a i) = 2) ∧ E = ⨆ i ∈ J, a i by
    intro E hE
    exact key _ E hE rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hE hn
  obtain ⟨hEel, -, hEw⟩ := hΩ E hE
  obtain ⟨i, A, hAE, hAS, hA2, hEI⟩ := hΩA E hE
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    have hbot : A = ⊥ := eq_bot_iff.mpr fun b hb => by
      by_contra hb1
      exact h ⟨b, hb, hb1⟩
    rw [hbot, Subgroup.card_bot] at hA2
    exact absurd hA2 (by norm_num)
  have haa : a * a = 1 := by
    have := pow_card_eq_one' (G := ↥A) (x := ⟨a, haA⟩)
    rw [hA2, pow_two] at this
    exact congrArg Subtype.val this
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEel.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set E₀ := E ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) (I i) with hE₀
  have hE₀I : ∀ e ∈ E₀, ∀ v ∈ I i, e v = v := fun e he v hv => he.2 v hv
  have hsplit : E = A ⊔ E₀ := by
    apply le_antisymm
    · intro e he
      obtain ⟨s, hs, hse⟩ := hext i e (hEI e he)
      have hsa : s * a = a * s := by
        refine linearEquiv_ext_of_planes hspan (fun v hv => ?_) fun j v hv => ?_
        · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, (hAS haA).2.1 v hv, hs.2.1 v hv,
            (hAS haA).2.1 v hv]
        · by_cases hj : j = i
          · subst hj
            have hav : a v ∈ I j := apply_mem_of_mem_submoduleStab (U := I j) (hAS haA).1 hv
            have hea := congrArg (fun g : V ≃ₗ[k] V => g v) (hEc e he a (hAE haA))
            simp only [LinearEquiv.mul_apply] at hea
            rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hse _ hav, hse v hv, hea]
          · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, (hAS haA).2.2 j hj v hv,
              hs.2.2 j hj v hv, (hAS haA).2.2 j hj v hv]
      have hsA : s ∈ A := by
        rcases hcent i a (hAS haA) ha1 haa s hs hsa with h | h
        · rw [h]
          exact one_mem A
        · rw [h]
          exact haA
      have he₀ : s⁻¹ * e ∈ E₀ := Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hAE hsA)) he,
        fun v hv => by
          show (s⁻¹ * e) v = v
          rw [LinearEquiv.mul_apply, ← hse v hv]
          exact gl_inv_apply s v⟩
      have he' : e = s * (s⁻¹ * e) := by group
      rw [he']
      exact mul_mem (Subgroup.mem_sup_left hsA) (Subgroup.mem_sup_right he₀)
    · exact sup_le hAE inf_le_left
  have hcomm : ∀ x ∈ A, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy => hEc x (hAE hx) y hy.1
  obtain ⟨h1, h2⟩ := card_sup_and_card_fixGL_sup hI hc (hdim i) hk hAS hA2 hE₀I hcomm
  rw [← hsplit] at h1 h2
  have hw : weight (MonoidHom.id (V ≃ₗ[k] V)) E₀ = weight (MonoidHom.id (V ≃ₗ[k] V)) E := by
    unfold weight
    rw [h1, ← h2]
    ring
  by_cases hE₀bot : E₀ = ⊥
  · refine ⟨{i}, Finset.singleton_nonempty i, fun _ => A, fun j hj => ?_, ?_⟩
    · rw [Finset.mem_singleton] at hj
      subst hj
      exact ⟨hAS, hA2⟩
    · rw [hsplit, hE₀bot, sup_bot_eq, Finset.iSup_singleton]
  · have hE₀Ω : E₀ ∈ Ω := hΩsub E hE E₀ inf_le_left hE₀bot (hw ▸ hEw)
    have hlt : Nat.card E₀ < n := by
      rw [← hn, h1]
      have := Nat.card_pos (α := E₀)
      omega
    obtain ⟨J₀, -, a₀, ha₀, hE₀eq⟩ := ih _ hlt E₀ hE₀Ω rfl
    have hiJ₀ : i ∉ J₀ := by
      intro hi
      obtain ⟨hai, hai2⟩ := ha₀ i hi
      have hle : a₀ i ≤ E₀ := by
        rw [hE₀eq]
        exact le_iSup₂_of_le (f := fun j (_ : j ∈ J₀) => a₀ j) i hi le_rfl
      have hbot : a₀ i = ⊥ := eq_bot_iff.mpr fun g hg =>
        eq_one_of_mem_planeSupport hspan (hai hg) (hE₀I g (hle hg))
      rw [hbot, Subgroup.card_bot] at hai2
      exact absurd hai2 (by norm_num)
    refine ⟨insert i J₀, Finset.insert_nonempty i J₀, Function.update a₀ i A, fun j hj => ?_, ?_⟩
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · rw [Function.update_self]
        exact ⟨hAS, hA2⟩
      · have hji : j ≠ i := fun h => hiJ₀ (h ▸ hj)
        rw [Function.update_of_ne hji]
        exact ha₀ j hj
    · rw [Finset.iSup_insert, Function.update_self, hsplit, hE₀eq]
      congr 1
      refine iSup_congr fun j => iSup_congr fun hj => ?_
      rw [Function.update_of_ne (fun (h : j = i) => hiJ₀ (h ▸ hj))]

theorem perm_three_centralizer_involution :
    ∀ σ τ : Equiv.Perm (Fin 3), τ * τ = 1 → τ ≠ 1 → σ * τ = τ * σ → σ = 1 ∨ σ = τ := by
  decide

theorem card_linearEquiv_plane [Finite k] (hk : Nat.card k = 2) {P : Submodule k V}
    [FiniteDimensional k P] (hP : finrank k P = 2) : Nat.card (P ≃ₗ[k] P) = 6 := by
  classical
  have : Fintype k := Fintype.ofFinite k
  let b : Module.Basis (Fin 2) k P := Module.finBasisOfFinrankEq k P hP
  let e : (P ≃ₗ[k] P) ≃* Matrix.GeneralLinearGroup (Fin 2) k :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k P).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hk]
  simp [Fin.prod_univ_two]

theorem planeSupport_perm_three [CharP k 2] [FiniteDimensional k V] [Finite k] {r : ℕ}
    {I : Fin r → Submodule k V} {V₀ : Submodule k V} (hc : IsCompl (⨆ j, I j) V₀) {i : Fin r}
    (hk : Nat.card k = 2) (hdim : finrank k (I i) = 2) {L A : Subgroup (V ≃ₗ[k] V)}
    (hS : L ⊔ A = planeSupport I V₀ i) (hL3 : Nat.card L = 3) (hA2 : Nat.card A = 2)
    (hirr : ∀ U : Submodule k V, U ≤ I i → (∀ x ∈ L, ∀ u ∈ U, x u ∈ U) → U = ⊥ ∨ U = I i)
    (hW : QuasithinUnique.Setup.Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) (I i))
    (hbij : Function.Bijective (resSub (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) (I i) hW)) :
    Nat.card (planeSupport I V₀ i) = 6 ∧
      Nonempty (planeSupport I V₀ i ≃* Equiv.Perm (Fin 3)) ∧
      ⁅planeSupport I V₀ i, planeSupport I V₀ i⁆ = L ∧
      ∀ a ∈ planeSupport I V₀ i, a ≠ 1 → a * a = 1 →
        ∀ s ∈ planeSupport I V₀ i, s * a = a * s → s = 1 ∨ s = a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hspan : (⨆ j, I j) ⊔ V₀ = ⊤ := codisjoint_iff.mp hc.2
  have : Finite V := Module.finite_of_finite k
  have : Finite (V ≃ₗ[k] V) :=
    Finite.of_injective (fun f : V ≃ₗ[k] V => (f : V → V)) DFunLike.coe_injective
  have hcard : Nat.card (planeSupport I V₀ i) = 6 := by
    rw [← hS, Nat.card_congr (Equiv.ofBijective _ hbij), card_linearEquiv_plane hk hdim]
  have hLS : L ≤ planeSupport I V₀ i := hS ▸ le_sup_left
  have hAS : A ≤ planeSupport I V₀ i := hS ▸ le_sup_right
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    have hbot : A = ⊥ := eq_bot_iff.mpr fun b hb => by
      by_contra hb1
      exact h ⟨b, hb, hb1⟩
    rw [hbot, Subgroup.card_bot] at hA2
    exact absurd hA2 (by norm_num)
  have haa : a * a = 1 := by
    have := pow_card_eq_one' (G := ↥A) (x := ⟨a, haA⟩)
    rw [hA2, pow_two] at this
    exact congrArg Subtype.val this
  obtain ⟨l, hlL, hla⟩ : ∃ l ∈ L, l * a ≠ a * l := by
    by_contra hall
    have hcomm : ∀ l ∈ L, l * a = a * l := fun l hl => by
      by_contra h
      exact hall ⟨l, hl, h⟩
    have hline := finrank_inf_ker_sub_one_eq_one (p := I i) hdim (a := (a : V →ₗ[k] V))
      (LinearMap.ext fun v => by
        have := congrArg (fun g : V ≃ₗ[k] V => g v) haa
        simpa using this)
      (fun v hv => apply_mem_of_mem_submoduleStab (U := I i) (hAS haA).1 hv)
      (by
        by_contra h
        apply ha1
        refine eq_one_of_mem_planeSupport hspan (hAS haA) fun v hv => ?_
        by_contra hv'
        exact h ⟨v, hv, hv'⟩)
    rcases hirr (I i ⊓ LinearMap.ker ((a : V →ₗ[k] V) - 1)) inf_le_left (fun x hx u hu => by
      refine ⟨apply_mem_of_mem_submoduleStab (U := I i) (hLS hx).1 hu.1, ?_⟩
      have hau : a u = u := by
        have := LinearMap.mem_ker.mp hu.2
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
        exact this
      refine LinearMap.mem_ker.mpr ?_
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      have hxa := congrArg (fun g : V ≃ₗ[k] V => g u) (hcomm x hx)
      simp only [LinearEquiv.mul_apply] at hxa
      show a (x u) = x u
      rw [← hxa, hau]) with h | h
    · rw [h, finrank_bot] at hline
      exact absurd hline (by norm_num)
    · rw [h, hdim] at hline
      exact absurd hline (by norm_num)
  have hne : (⟨l, hLS hlL⟩ : planeSupport I V₀ i) * ⟨a, hAS haA⟩ ≠
      ⟨a, hAS haA⟩ * ⟨l, hLS hlL⟩ := fun h => hla (congrArg Subtype.val h)
  obtain ⟨φ⟩ := CFSG.GH74.M12.Hyp.nonempty_mulEquiv_perm_three_of_card_six hcard _ _ hne
  refine ⟨hcard, ⟨φ⟩, ?_, ?_⟩
  ·
    have hrel : L.relIndex (planeSupport I V₀ i) = 2 := by
      have h := Subgroup.relIndex_mul_card L (planeSupport I V₀ i)
      rw [inf_eq_left.mpr hLS, hL3, hcard] at h
      omega
    have hidx : (L.subgroupOf (planeSupport I V₀ i)).index = 2 := hrel
    have hle : ⁅planeSupport I V₀ i, planeSupport I V₀ i⁆ ≤ L := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      have h1 : (⟨x, hx⟩ : planeSupport I V₀ i) * ⟨y, hy⟩ * (⟨x, hx⟩ : planeSupport I V₀ i)⁻¹ *
          (⟨y, hy⟩ : planeSupport I V₀ i)⁻¹ ∈ L.subgroupOf (planeSupport I V₀ i) := by
        rw [mul_assoc, Subgroup.mul_mem_iff_of_index_two hidx,
          Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
          inv_mem_iff, inv_mem_iff]
      exact h1
    have hne' : ⁅planeSupport I V₀ i, planeSupport I V₀ i⁆ ≠ ⊥ := by
      intro h
      apply hla
      have hm : ⁅l, a⁆ ∈ ⁅planeSupport I V₀ i, planeSupport I V₀ i⁆ :=
        Subgroup.commutator_mem_commutator (hLS hlL) (hAS haA)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hm
    have hdvd : Nat.card ↥(⁅planeSupport I V₀ i, planeSupport I V₀ i⁆ :
        Subgroup (V ≃ₗ[k] V)) ∣ 3 :=
      hL3 ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hne'
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [h, hL3])
  · intro b hb hb1 hbb s hs hsb
    have h1 : φ ⟨b, hb⟩ * φ ⟨b, hb⟩ = 1 := by
      rw [← map_mul]
      have : (⟨b, hb⟩ : planeSupport I V₀ i) * ⟨b, hb⟩ = 1 := Subtype.ext hbb
      rw [this, map_one]
    have h2 : φ ⟨b, hb⟩ ≠ 1 := by
      intro h
      apply hb1
      have := φ.injective (h.trans (map_one φ).symm)
      exact congrArg Subtype.val this
    have h3 : φ ⟨s, hs⟩ * φ ⟨b, hb⟩ = φ ⟨b, hb⟩ * φ ⟨s, hs⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hsb
    rcases perm_three_centralizer_involution _ _ h1 h2 h3 with h | h
    · left
      have := φ.injective (h.trans (map_one φ).symm)
      exact congrArg Subtype.val this
    · right
      have := φ.injective h
      exact congrArg Subtype.val this

theorem isElementaryAbelian_mono {p : ℕ} {G : Type*} [Group G] {E E₀ : Subgroup G}
    (h : E₀ ≤ E) [hE : IsElementaryAbelian p E] : IsElementaryAbelian p E₀ :=
  CFSG.IsElementaryAbelian.of_le inferInstance h

theorem map_commGL_eq_of_mem_normalizer {L : Subgroup (V ≃ₗ[k] V)} {x : V ≃ₗ[k] V}
    (hx : x ∈ Subgroup.normalizer (L : Set (V ≃ₗ[k] V))) :
    (commGL L ⊤).map (x : V →ₗ[k] V) = commGL L ⊤ := by
  rw [← commGL_conjSub, conjSub_eq_self hx]

theorem mem_normalizer_commutator_of_mem {N A : Subgroup (V ≃ₗ[k] V)} {x : V ≃ₗ[k] V}
    (hN : x ∈ Subgroup.normalizer (N : Set (V ≃ₗ[k] V)))
    (hA : x ∈ Subgroup.normalizer (A : Set (V ≃ₗ[k] V))) :
    x ∈ Subgroup.normalizer ((⁅N, A⁆ : Subgroup (V ≃ₗ[k] V)) : Set (V ≃ₗ[k] V)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show conjSub x ⁅N, A⁆ = ⁅N, A⁆
  rw [← commutator_conjSub_conjSub, conjSub_eq_self hN, conjSub_eq_self hA]

theorem map_eq_self_of_fix {U : Submodule k V} {g : V ≃ₗ[k] V} (hg : ∀ u ∈ U, g u = u) :
    U.map (g : V →ₗ[k] V) = U := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    show g u ∈ U
    rw [hg u hu]
    exact hu
  · intro u hu
    exact ⟨u, hu, hg u hu⟩

theorem commGL_mono {H K : Subgroup (V ≃ₗ[k] V)} (h : H ≤ K) : commGL H ⊤ ≤ commGL K ⊤ :=
  Submodule.span_mono fun _ ⟨b, hb, u, hu, hw⟩ => ⟨b, h hb, u, hu, hw⟩

theorem weight_bot_eq [Finite V] : weight (MonoidHom.id (V ≃ₗ[k] V)) ⊥ = Nat.card V := by
  unfold weight
  rw [Subgroup.card_bot, one_mul]
  have htop : fixSub (MonoidHom.id (V ≃ₗ[k] V)) ⊥ = ⊤ := by
    ext v
    simp only [mem_fixSub, Subgroup.mem_bot, Submodule.mem_top, iff_true]
    rintro b rfl
    rfl
  rw [htop]
  exact Nat.card_congr (Equiv.Set.univ V)

@[expose] def offenderSet (G : Subgroup (V ≃ₗ[k] V)) : Set (Subgroup (V ≃ₗ[k] V)) :=
  {A | A ≤ G ∧ A ≠ ⊥ ∧ IsElementaryAbelian 2 A ∧
    Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A}

@[expose] def minOffenderSet (G : Subgroup (V ≃ₗ[k] V)) : Set (Subgroup (V ≃ₗ[k] V)) :=
  {A | A ∈ offenderSet G ∧ ∀ C : Subgroup (V ≃ₗ[k] V), ⊥ < C → C < A →
    weight (MonoidHom.id (V ≃ₗ[k] V)) C < weight (MonoidHom.id (V ≃ₗ[k] V)) A}

theorem mem_minOffenderSet_iff {G A : Subgroup (V ≃ₗ[k] V)} :
    A ∈ minOffenderSet G ↔ IsMinOffender G A :=
  ⟨fun ⟨⟨h1, h2, h3, h4⟩, h5⟩ => ⟨h1, h2, h3, h4, h5⟩,
    fun ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨h1, h2, h3, h4⟩, h5⟩⟩

abbrev naturalFactor {r : ℕ} (L : Fin r → Subgroup (V ≃ₗ[k] V)) (i : Fin r) :
    Subgroup (V ≃ₗ[k] V) :=
  planeSupport (fun j => commGL (L j) ⊤) (fixGL (⨆ j, L j)) i

structure OffenderS3Products (G : Subgroup (V ≃ₗ[k] V)) {r : ℕ}
    (L : Fin r → Subgroup (V ≃ₗ[k] V)) : Prop where
  card_L : ∀ i, Nat.card (L i) = 3
  L_comm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x
  L_indep : iSupIndep L
  D_le : (⨆ i, L i) ≤ G
  D_normal : ((⨆ i, L i).subgroupOf G).Normal
  I_indep : iSupIndep fun i => commGL (L i) ⊤
  V_compl : IsCompl (⨆ i, commGL (L i) ⊤) (fixGL (⨆ i, L i))
  finrank_I : ∀ i, finrank k (commGL (L i) ⊤) = 2
  S_le : ∀ i, naturalFactor L i ≤ G
  S_iso : ∀ i, Nonempty (naturalFactor L i ≃* Equiv.Perm (Fin 3))
  S_derived : ∀ i, ⁅naturalFactor L i, naturalFactor L i⁆ = L i
  S_comm : ∀ i j, i ≠ j → ∀ x ∈ naturalFactor L i, ∀ y ∈ naturalFactor L j, x * y = y * x
  S_indep : iSupIndep (naturalFactor L)
  B_eq : (⨆ A ∈ offenderSet G, A) = ⨆ i, naturalFactor L i
  B_normal : ((⨆ i, naturalFactor L i).subgroupOf G).Normal
  B_comm : commGL (⨆ i, naturalFactor L i) ⊤ = ⨆ i, commGL (L i) ⊤
  B_fix : fixGL (⨆ i, naturalFactor L i) = fixGL (⨆ i, L i)
  perm : ∀ x ∈ G, ∀ i, ∃ j, conjSub x (naturalFactor L i) = naturalFactor L j ∧
    conjSub x (L i) = L j ∧ (commGL (L i) ⊤).map (x : V →ₗ[k] V) = commGL (L j) ⊤
  offender_iff : ∀ A, A ∈ offenderSet G ↔ ∃ J : Finset (Fin r), J.Nonempty ∧
    ∃ a : Fin r → Subgroup (V ≃ₗ[k] V),
      (∀ i ∈ J, a i ≤ naturalFactor L i ∧ Nat.card (a i) = 2) ∧ A = ⨆ i ∈ J, a i
  weight_eq : ∀ A ∈ offenderSet G, weight (MonoidHom.id (V ≃ₗ[k] V)) A = Nat.card V
  min_iff : ∀ A, A ∈ minOffenderSet G ↔ ∃ i, A ≤ naturalFactor L i ∧ Nat.card A = 2
  weight_le : ∀ A ≤ G, IsElementaryAbelian 2 A →
    weight (MonoidHom.id (V ≃ₗ[k] V)) A ≤ Nat.card V

theorem solvable_faithful_offenders_generate_natural_S3_products [Finite k] [CharP k 2]
    [FiniteDimensional k V] {G : Subgroup (V ≃ₗ[k] V)} (hsolv : Group.IsSolvable G)
    (hO2 : CFSG.pCore 2 G = ⊥) (hΩ : (offenderSet G).Nonempty) :
    Nat.card k = 2 ∧ (∀ A ∈ minOffenderSet G, Nat.card A = 2) ∧
      ∃ (r : ℕ) (L : Fin r → Subgroup (V ≃ₗ[k] V)), 1 ≤ r ∧ Function.Injective L ∧
        Set.range L = (fun A => ⁅(CFSG.fittingSubgroup G).map G.subtype, A⁆) '' minOffenderSet G ∧
        OffenderS3Products G L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite V := Module.finite_of_finite k
  have : Finite (V ≃ₗ[k] V) :=
    Finite.of_injective (fun f : V ≃ₗ[k] V => (f : V → V)) DFunLike.coe_injective
  set F := (CFSG.fittingSubgroup ↥G).map G.subtype with hF
  have hFG : F ≤ G := Subgroup.map_subtype_le _
  have hFsub : F.subgroupOf G = CFSG.fittingSubgroup ↥G :=
    Subgroup.comap_map_eq_self_of_injective G.subtype_injective _
  have hFn : (F.subgroupOf G).Normal := by
    rw [hFsub]
    exact CFSG.fittingSubgroup_normal
  let eF : ↥(CFSG.fittingSubgroup ↥G) ≃* ↥F :=
    (CFSG.fittingSubgroup ↥G).equivMapOfInjective G.subtype G.subtype_injective
  have : Group.IsNilpotent ↥F := Group.nilpotent_of_mulEquiv eF
  have hFodd : Odd (Nat.card F) := by
    rw [← Nat.card_congr eF.toEquiv]
    exact CFSG.QuasithinUnique.Setup.Wreath.odd_card_fittingSubgroup hO2
  have hCF : G ⊓ Subgroup.centralizer (F : Set (V ≃ₗ[k] V)) ≤ F := by
    rintro x ⟨hxG, hxC⟩
    have h1 : (⟨x, hxG⟩ : ↥G) ∈ Subgroup.centralizer
        ((CFSG.fittingSubgroup ↥G : Subgroup ↥G) : Set ↥G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : (y : V ≃ₗ[k] V) ∈ F := ⟨y, hy, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 hxC _ hy'
      exact Subtype.ext (by simpa using this)
    have h2 := CFSG.QuasithinUnique.Setup.Wreath.solvable_fitting_self_centralizing hsolv h1
    exact ⟨⟨x, hxG⟩, h2, rfl⟩
  have hGNF : G ≤ Subgroup.normalizer (F : Set (V ≃ₗ[k] V)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFG).mp hFn
  have hcommF : ∀ A, IsMinOffender G A → ⁅F, A⁆ ≠ ⊥ := by
    intro A hA hbot
    have hAC : A ≤ Subgroup.centralizer (F : Set (V ≃ₗ[k] V)) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
    have hAF : A ≤ F := (le_inf hA.1 hAC).trans hCF
    have := hA.2.2.1
    have hA2 : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA2
    have hdvd : Nat.card A ∣ Nat.card F := Subgroup.card_dvd_of_le hAF
    rcases n with _ | n
    · exact hA.2.1 (Subgroup.card_eq_one.mp (by rw [hn, pow_zero]))
    · rw [hn, pow_succ] at hdvd
      exact (Nat.not_even_iff_odd.mpr hFodd)
        (even_iff_two_dvd.mpr ((Dvd.intro_left _ rfl).trans hdvd))
  have hnat : ∀ A, IsMinOffender G A → Nat.card k = 2 ∧ Nat.card A = 2 ∧
      Nat.card ↥(⁅F, A⁆ : Subgroup (V ≃ₗ[k] V)) = 3 ∧ finrank k ↥(commGL ⁅F, A⁆ ⊤) = 2 ∧
      (∃ hW : QuasithinUnique.Setup.Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (⁅F, A⁆ ⊔ A)
          (commGL ⁅F, A⁆ ⊤),
        Function.Bijective
          (resSub (MonoidHom.id (V ≃ₗ[k] V)) (⁅F, A⁆ ⊔ A) (commGL ⁅F, A⁆ ⊤) hW)) ∧
      commGL ⁅F, A⁆ ⊤ ⊔ fixGL A = ⊤ ∧
      weight (MonoidHom.id (V ≃ₗ[k] V)) A = Nat.card V := by
    intro A hA
    obtain ⟨h1, h2, -, h4, -, -, h7, h8, h9, h10, -⟩ :=
      nilpotent_offender_natural_S3_factors.{_, _, 0} hFG hFn hFodd hA.1 hA.2.2.1 hA.2.1
        hA.2.2.2.1 hA.2.2.2.2 (hcommF A hA)
    exact ⟨h1, h2, h4, h7, h8, h9, h10⟩
  obtain ⟨E₁, hE₁⟩ := hΩ
  obtain ⟨A₁, hA₁⟩ := exists_minOffender (H := E₁) le_rfl hE₁.2.1 hE₁.2.2.1 hE₁.2.2.2
  have hA₁G : IsMinOffender G A₁ := ⟨hA₁.1.trans hE₁.1, hA₁.2⟩
  have hk : Nat.card k = 2 := (hnat A₁ hA₁G).1
  set 𝓛 := (fun A => ⁅F, A⁆) '' minOffenderSet G with h𝓛
  obtain ⟨r, L, hLinj, hLrange⟩ : ∃ (r : ℕ) (L : Fin r → Subgroup (V ≃ₗ[k] V)),
      Function.Injective L ∧ Set.range L = 𝓛 := by
    have : Fintype ↥𝓛 := (Set.toFinite 𝓛).fintype
    refine ⟨Fintype.card 𝓛, fun i => ((Fintype.equivFin 𝓛).symm i : Subgroup _), ?_, ?_⟩
    · intro i j hij
      exact (Fintype.equivFin 𝓛).symm.injective (Subtype.ext hij)
    · ext X
      constructor
      · rintro ⟨i, rfl⟩
        exact ((Fintype.equivFin 𝓛).symm i).2
      · intro hX
        exact ⟨Fintype.equivFin 𝓛 ⟨X, hX⟩, by simp⟩
  have hLmem : ∀ i, ∃ B, IsMinOffender G B ∧ ⁅F, B⁆ = L i := by
    intro i
    have h : L i ∈ 𝓛 := hLrange ▸ ⟨i, rfl⟩
    obtain ⟨B, hB, hBL⟩ := h
    exact ⟨B, mem_minOffenderSet_iff.mp hB, hBL⟩
  have hin𝓛 : ∀ B, IsMinOffender G B → ∃ i, ⁅F, B⁆ = L i := by
    intro B hB
    have h : ⁅F, B⁆ ∈ Set.range L := hLrange ▸ ⟨B, mem_minOffenderSet_iff.mpr hB, rfl⟩
    obtain ⟨i, hi⟩ := h
    exact ⟨i, hi.symm⟩
  choose A hAmin hAL using hLmem
  obtain ⟨i₁, -⟩ := hin𝓛 A₁ hA₁G
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr fun h => by subst h; exact i₁.elim0
  have hL3 : ∀ i, Nat.card (L i) = 3 := fun i => hAL i ▸ (hnat _ (hAmin i)).2.2.1
  have hrk : ∀ i, finrank k (commGL (L i) ⊤) = 2 := fun i =>
    hAL i ▸ (hnat _ (hAmin i)).2.2.2.1
  have hLF : ∀ i, L i ≤ F := by
    intro i
    rw [← hAL i, Subgroup.commutator_le]
    intro f hf a ha
    have h1 : a * f⁻¹ * a⁻¹ ∈ F :=
      (Subgroup.mem_normalizer_iff.mp (hGNF ((hAmin i).1 ha)) f⁻¹).mp (inv_mem hf)
    have h2 := mul_mem hf h1
    simpa [commutatorElement_def, mul_assoc] using h2
  have hD3 : IsPGroup 3 (⨆ i, L i : Subgroup (V ≃ₗ[k] V)) := by
    let P : Sylow 3 ↥F := default
    have hP : ∀ i, L i ≤ (P : Subgroup ↥F).map F.subtype := by
      intro i
      have h3 : IsPGroup 3 ((L i).subgroupOf F) :=
        (IsPGroup.of_card (n := 1) (by rw [hL3 i]; norm_num)).comap_of_injective F.subtype
          F.subtype_injective
      obtain ⟨Q, hQ⟩ := h3.exists_le_sylow
      have : Unique (Sylow 3 ↥F) := Sylow.unique_of_normal P inferInstance
      have hQP : Q = P := Subsingleton.elim _ _
      intro x hx
      exact ⟨⟨x, hLF i hx⟩, hQP ▸ hQ hx, rfl⟩
    exact (P.isPGroup'.map F.subtype).to_le (iSup_le hP)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, -⟩ :=
    binary_three_group_rank_two_generators_disjoint_natural_planes hk L hLinj
      (fun i => isCyclic_of_prime_card (hL3 i)) hL3 hD3 hrk
  set I : Fin r → Submodule k V := fun i => commGL (L i) ⊤ with hIdef
  set V₀ := fixGL (⨆ i, L i) with hV₀
  have hI : iSupIndep I := c3
  have hc : IsCompl (⨆ i, I i) V₀ := by
    rw [hIdef, hV₀, ← c4]
    exact c5
  have hspan : (⨆ j, I j) ⊔ V₀ = ⊤ := codisjoint_iff.mp hc.2
  have hconjL : ∀ x ∈ G, ∀ i, ∃ j, conjSub x (L i) = L j := by
    intro x hx i
    obtain ⟨j, hj⟩ := hin𝓛 _ ((hAmin i).conj hx)
    refine ⟨j, ?_⟩
    rw [← hAL i, ← commutator_conjSub (hGNF hx), hj]
  have hDG : (⨆ i, L i) ≤ G := iSup_le fun i => (hLF i).trans hFG
  have hDn : G ≤ Subgroup.normalizer ((⨆ i, L i : Subgroup (V ≃ₗ[k] V)) : Set (V ≃ₗ[k] V)) := by
    have hle : ∀ y ∈ G, conjSub y (⨆ i, L i) ≤ ⨆ i, L i := by
      intro y hy
      rw [OrderIso.map_iSup]
      refine iSup_le fun i => ?_
      obtain ⟨j, hj⟩ := hconjL y hy i
      rw [hj]
      exact le_iSup L j
    intro x hx
    exact mem_normalizer_of_conjSub_le (hle x hx) (hle x⁻¹ (inv_mem hx))
  have hV₀G : ∀ x ∈ G, ∀ v ∈ V₀, x v ∈ V₀ := by
    intro x hx v hv
    have h1 := fixGL_conjSub x (⨆ i, L i)
    rw [conjSub_eq_self (hDn hx)] at h1
    rw [hV₀, h1]
    exact ⟨v, hv, rfl⟩
  have hIG : ∀ x ∈ G, ∀ j, ∃ j', (I j).map (x : V →ₗ[k] V) = I j' := by
    intro x hx j
    obtain ⟨j', hj'⟩ := hconjL x hx j
    exact ⟨j', by rw [← commGL_conjSub, hj']⟩
  have hkey : ∀ B, IsMinOffender G B → ∀ i, ⁅F, B⁆ = L i → L i ⊔ B = naturalFactor L i := by
    intro B hB i hBi
    obtain ⟨-, -, -, -, hbij, hsum, -⟩ := hnat B hB
    rw [hBi] at hbij hsum
    obtain ⟨hW, hbij⟩ := hbij
    refine sup_eq_planeSupport hI hc ?_ ?_ ?_ ?_ hsum hW hbij.2
    · intro l hl
      exact ⟨map_commGL_eq_of_mem_normalizer (Subgroup.le_normalizer hl), c8 i l hl,
        fun j hj v hv => c7 i j (Ne.symm hj) l hl v hv⟩
    · intro a ha
      have hn : a ∈ Subgroup.normalizer (L i : Set (V ≃ₗ[k] V)) := by
        rw [← hBi]
        exact mem_normalizer_commutator_of_mem (hGNF (hB.1 ha)) (Subgroup.le_normalizer ha)
      exact map_commGL_eq_of_mem_normalizer hn
    · exact fun a ha => hV₀G a (hB.1 ha)
    · exact fun a ha => hIG a (hB.1 ha)
  have hS : ∀ i, L i ⊔ A i = naturalFactor L i := fun i => hkey _ (hAmin i) i (hAL i)
  have hLS : ∀ i, L i ≤ naturalFactor L i := fun i => (hS i) ▸ le_sup_left
  have hSG : ∀ i, naturalFactor L i ≤ G := fun i =>
    (hS i) ▸ sup_le ((hLF i).trans hFG) (hAmin i).1
  have hS3 : ∀ i, Nat.card (naturalFactor L i) = 6 ∧
      Nonempty (naturalFactor L i ≃* Equiv.Perm (Fin 3)) ∧
      ⁅naturalFactor L i, naturalFactor L i⁆ = L i ∧
      ∀ a ∈ naturalFactor L i, a ≠ 1 → a * a = 1 →
        ∀ s ∈ naturalFactor L i, s * a = a * s → s = 1 ∨ s = a := by
    intro i
    obtain ⟨-, hA2, -, -, hbij, -, -⟩ := hnat _ (hAmin i)
    rw [hAL i] at hbij
    obtain ⟨hW, hbij⟩ := hbij
    exact planeSupport_perm_three hc hk (hrk i) (hS i) (hL3 i) hA2 (c6 i) hW hbij
  have hext : ∀ i (e : V ≃ₗ[k] V), (I i).map (e : V →ₗ[k] V) = I i →
      ∃ s ∈ naturalFactor L i, ∀ v ∈ I i, s v = e v := by
    intro i e he
    obtain ⟨-, -, -, -, hbij, -, -⟩ := hnat _ (hAmin i)
    rw [hAL i] at hbij
    obtain ⟨hW, hbij⟩ := hbij
    obtain ⟨t, ht⟩ := hbij.2 (e.ofSubmodules (I i) (I i) he)
    refine ⟨t, (hS i) ▸ t.2, fun v hv => ?_⟩
    have := congrArg (fun f : I i ≃ₗ[k] I i => ((f ⟨v, hv⟩ : I i) : V)) ht
    simpa [resSub_apply] using this
  have hΩsub : ∀ E ∈ offenderSet G, ∀ E₀ ≤ E, E₀ ≠ ⊥ →
      Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) E₀ → E₀ ∈ offenderSet G := by
    intro E hE E₀ hE₀ hne hw
    have := hE.2.2.1
    exact ⟨hE₀.trans hE.1, hne, isElementaryAbelian_mono hE₀, hw⟩
  have hΩA : ∀ E ∈ offenderSet G, ∃ i, ∃ B ≤ E, B ≤ naturalFactor L i ∧ Nat.card B = 2 ∧
      ∀ e ∈ E, (I i).map (e : V →ₗ[k] V) = I i := by
    intro E hE
    obtain ⟨B, hB⟩ := exists_minOffender (H := E) le_rfl hE.2.1 hE.2.2.1 hE.2.2.2
    have hBG : IsMinOffender G B := ⟨hB.1.trans hE.1, hB.2⟩
    obtain ⟨i, hi⟩ := hin𝓛 B hBG
    refine ⟨i, B, hB.1, (hkey B hBG i hi) ▸ le_sup_right, (hnat B hBG).2.1, fun e he => ?_⟩
    have hEc := hE.2.2.1
    have hcm : ∀ h ∈ E, e * h = h * e := fun h hh =>
      congrArg Subtype.val (hEc.toIsMulCommutative.is_comm.comm ⟨e, he⟩ ⟨h, hh⟩)
    have heB : e ∈ Subgroup.normalizer (B : Set (V ≃ₗ[k] V)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        rw [hcm h (hB.1 hh), mul_inv_cancel_right]
        exact hh
      · intro hh
        have hhE : h ∈ E := by
          have h1 : e * h * e⁻¹ ∈ E := hB.1 hh
          have h2 : h = e⁻¹ * (e * h * e⁻¹) * e := by group
          rw [h2]
          exact mul_mem (mul_mem (inv_mem he) h1) he
        rw [hcm h hhE, mul_inv_cancel_right] at hh
        exact hh
    have hn : e ∈ Subgroup.normalizer (L i : Set (V ≃ₗ[k] V)) := by
      rw [← hi]
      exact mem_normalizer_commutator_of_mem (hGNF (hE.1 he)) heB
    exact map_commGL_eq_of_mem_normalizer hn
  have hcoord := eq_coordProduct_of_mem hI hc hrk hk (fun i => (hS3 i).2.2.2) hext
    (offenderSet G) (fun E hE => ⟨hE.2.2.1, hE.2.1, hE.2.2.2⟩) hΩsub hΩA
  have hcoordΩ : ∀ (J : Finset (Fin r)) (a : Fin r → Subgroup (V ≃ₗ[k] V)), J.Nonempty →
      (∀ i ∈ J, a i ≤ naturalFactor L i ∧ Nat.card (a i) = 2) →
      (⨆ i ∈ J, a i) ∈ offenderSet G ∧
        weight (MonoidHom.id (V ≃ₗ[k] V)) (⨆ i ∈ J, a i) = Nat.card V := by
    intro J a hJ ha
    obtain ⟨hcard, hw⟩ := card_and_weight_coordProduct hI hc hrk hk a J ha
    refine ⟨⟨iSup₂_le fun i hi => (ha i hi).1.trans (hSG i), fun hbot => ?_,
      isElementaryAbelian_coordProduct hspan a J ha, hw.ge⟩, hw⟩
    rw [hbot, Subgroup.card_bot] at hcard
    have := Nat.one_lt_two_pow (Finset.card_pos.mpr hJ).ne'
    omega
  have hAΩ : ∀ i, A i ∈ offenderSet G := fun i =>
    ⟨(hAmin i).1, (hAmin i).2.1, (hAmin i).2.2.1, (hAmin i).2.2.2.1⟩
  have hperm : ∀ x ∈ G, ∀ i, ∃ j, conjSub x (naturalFactor L i) = naturalFactor L j ∧
      conjSub x (L i) = L j ∧ (commGL (L i) ⊤).map (x : V →ₗ[k] V) = commGL (L j) ⊤ := by
    intro x hx i
    obtain ⟨j, hj⟩ := hconjL x hx i
    refine ⟨j, ?_, hj, by rw [← commGL_conjSub, hj]⟩
    have hB : IsMinOffender G (conjSub x (A i)) := (hAmin i).conj hx
    have hBj : ⁅F, conjSub x (A i)⁆ = L j := by
      rw [commutator_conjSub (hGNF hx), hAL i, hj]
    rw [← hS i, OrderIso.map_sup, hj, hkey _ hB j hBj]
  have hBeq : (⨆ A ∈ offenderSet G, A) = ⨆ i, naturalFactor L i := by
    apply le_antisymm
    · refine iSup₂_le fun E hE => ?_
      obtain ⟨J, -, a, ha, rfl⟩ := hcoord E hE
      exact iSup₂_le fun i hi => (ha i hi).1.trans (le_iSup (naturalFactor L) i)
    · refine iSup_le fun i => ?_
      rw [← hS i]
      refine sup_le ?_ (le_iSup₂_of_le (f := fun (A : Subgroup (V ≃ₗ[k] V))
        (_ : A ∈ offenderSet G) => A) (A i) (hAΩ i) le_rfl)
      rw [← hAL i, Subgroup.commutator_le]
      intro f hf a ha
      have hfG : f ∈ G := hFG hf
      have h1 : f * a * f⁻¹ ∈ conjSub f (A i) := conjSub_mem_of_mem ha
      have hcΩ : conjSub f (A i) ∈ offenderSet G :=
        let h := (hAmin i).conj hfG
        ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
      have h2 : f * a * f⁻¹ ∈ ⨆ A ∈ offenderSet G, A :=
        le_iSup₂_of_le (f := fun (A : Subgroup (V ≃ₗ[k] V)) (_ : A ∈ offenderSet G) => A)
          _ hcΩ le_rfl h1
      have h3 : a⁻¹ ∈ ⨆ A ∈ offenderSet G, A :=
        le_iSup₂_of_le (f := fun (A : Subgroup (V ≃ₗ[k] V)) (_ : A ∈ offenderSet G) => A)
          (A i) (hAΩ i) le_rfl (inv_mem ha)
      rw [commutatorElement_def]
      exact mul_mem h2 h3
  have hSsupG : (⨆ i, naturalFactor L i) ≤ G := iSup_le hSG
  have hBn : G ≤ Subgroup.normalizer
      ((⨆ i, naturalFactor L i : Subgroup (V ≃ₗ[k] V)) : Set (V ≃ₗ[k] V)) := by
    have hle : ∀ y ∈ G, conjSub y (⨆ i, naturalFactor L i) ≤ ⨆ i, naturalFactor L i := by
      intro y hy
      rw [OrderIso.map_iSup]
      refine iSup_le fun i => ?_
      obtain ⟨j, hj, -⟩ := hperm y hy i
      rw [hj]
      exact le_iSup (naturalFactor L) j
    intro x hx
    exact mem_normalizer_of_conjSub_le (hle x hx) (hle x⁻¹ (inv_mem hx))
  have hBcomm : commGL (⨆ i, naturalFactor L i) ⊤ = ⨆ i, commGL (L i) ⊤ := by
    apply le_antisymm
    · have hK : (⨆ i, naturalFactor L i) ≤
          submoduleStab (⨆ j, I j) ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) V₀ := by
        refine iSup_le fun i g hg => ⟨?_, fun v hv => hg.2.1 v hv⟩
        show (⨆ j, I j).map (g : V →ₗ[k] V) = ⨆ j, I j
        rw [Submodule.map_iSup]
        refine iSup_congr fun j => ?_
        by_cases hji : j = i
        · subst hji
          exact hg.1
        · exact map_eq_self_of_fix (hg.2.2 j hji)
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨b, hb, u, -, rfl⟩
      obtain ⟨hb1, hb2⟩ := hK hb
      have hu : u ∈ (⨆ j, I j) ⊔ V₀ := hspan ▸ Submodule.mem_top
      obtain ⟨w, hw, v₀, hv₀, rfl⟩ := Submodule.mem_sup.mp hu
      have hbv₀ : b v₀ = v₀ := hb2 v₀ hv₀
      have hbw : b w ∈ ⨆ j, I j := apply_mem_of_mem_submoduleStab hb1 hw
      show (MonoidHom.id (V ≃ₗ[k] V)) b (w + v₀) - (w + v₀) ∈ ⨆ j, I j
      rw [MonoidHom.id_apply, map_add, hbv₀, show b w + v₀ - (w + v₀) = b w - w by abel]
      exact Submodule.sub_mem _ hbw hw
    · exact iSup_le fun i => commGL_mono ((hLS i).trans (le_iSup (naturalFactor L) i))
  have hBfix : fixGL (⨆ i, naturalFactor L i) = fixGL (⨆ i, L i) := by
    apply le_antisymm
    · exact fixSub_anti _ (iSup_mono hLS)
    · have hle : (⨆ i, naturalFactor L i) ≤ centSub (MonoidHom.id (V ≃ₗ[k] V)) V₀ :=
        iSup_le fun i g hg v hv => hg.2.1 v hv
      intro v hv g hg
      exact hle hg v hv
  refine ⟨hk, fun B hB => (hnat B (mem_minOffenderSet_iff.mp hB)).2.1, r, L, hr, hLinj, hLrange,
    ?_⟩
  exact
    { card_L := hL3
      L_comm := c1
      L_indep := c2
      D_le := hDG
      D_normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDG).mpr hDn
      I_indep := c3
      V_compl := hc
      finrank_I := hrk
      S_le := hSG
      S_iso := fun i => (hS3 i).2.1
      S_derived := fun i => (hS3 i).2.2.1
      S_comm := fun i j hij x hx y hy => planeSupport_commute hspan hij hx hy
      S_indep := iSupIndep_planeSupport hspan
      B_eq := hBeq
      B_normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSsupG).mpr hBn
      B_comm := hBcomm
      B_fix := hBfix
      perm := hperm
      offender_iff := fun B => ⟨hcoord B, fun ⟨J, hJ, a, ha, hBa⟩ => hBa ▸ (hcoordΩ J a hJ ha).1⟩
      weight_eq := fun B hB => by
        obtain ⟨J, hJ, a, ha, rfl⟩ := hcoord B hB
        exact (hcoordΩ J a hJ ha).2
      min_iff := fun B => by
        constructor
        · intro hB
          have hB' := mem_minOffenderSet_iff.mp hB
          obtain ⟨i, hi⟩ := hin𝓛 B hB'
          exact ⟨i, (hkey B hB' i hi) ▸ le_sup_right, (hnat B hB').2.1⟩
        · rintro ⟨i, hBS, hB2⟩
          have hBΩ : B ∈ offenderSet G := by
            have := (hcoordΩ {i} (fun _ => B) (Finset.singleton_nonempty i) (fun j hj => by
              rw [Finset.mem_singleton] at hj
              subst hj
              exact ⟨hBS, hB2⟩)).1
            rwa [Finset.iSup_singleton] at this
          refine ⟨hBΩ, fun C hC1 hC2 => ?_⟩
          exfalso
          have hdvd : Nat.card C ∣ 2 := hB2 ▸ Subgroup.card_dvd_of_le hC2.le
          rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
          · exact (bot_lt_iff_ne_bot.mp hC1) (Subgroup.card_eq_one.mp h)
          · exact hC2.ne (Subgroup.eq_of_le_of_card_ge hC2.le (by rw [h, hB2]))
      weight_le := fun B hBG hBe => by
        by_cases hbot : B = ⊥
        · rw [hbot, weight_bot_eq]
        · by_cases hw : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) B
          · have hBΩ : B ∈ offenderSet G := ⟨hBG, hbot, hBe, hw⟩
            obtain ⟨J, hJ, a, ha, rfl⟩ := hcoord B hBΩ
            exact (hcoordΩ J a hJ ha).2.le
          · exact (not_le.mp hw).le }

end CFSG.Quasithin.SteinbergCF
