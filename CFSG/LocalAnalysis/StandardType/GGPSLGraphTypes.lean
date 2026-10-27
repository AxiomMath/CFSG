module

public import CFSG.LocalAnalysis.StandardType.GGPSLGraphAlgebra
public import CFSG.LocalAnalysis.StandardType.GGBlockEmbed
public import CFSG.LocalAnalysis.StandardType.GGHermTools
public import CFSG.LocalAnalysis.StandardType.GGFormTransvection
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALangHerm

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition CFSG.StandardType.ClassicalPosition.Geo Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private lemma pslBT_solvable_of_forall_perfect_eq_bot {G : Type} [Group G] [Finite G]
    (h : ∀ Y : Subgroup G, Group.IsPerfect ↥Y → Y = ⊥) : Group.IsSolvable G := by
  by_contra hns
  have hne : ∀ n, derivedSeries G n ≠ ⊥ := fun n hn => hns ⟨n, hn⟩
  have hstrict : ∀ n, derivedSeries G (n + 1) < derivedSeries G n := by
    intro n
    refine lt_of_le_of_ne (derivedSeries_antitone G (Nat.le_succ n)) ?_
    intro heq
    apply hne n
    have hperf : Group.IsPerfect ↥(derivedSeries G n) := by
      rw [Subgroup.isPerfect_iff]
      rw [← derivedSeries_succ]
      exact heq
    exact h (derivedSeries G n) hperf
  have hcard : ∀ n, Nat.card (derivedSeries G n) + n ≤ Nat.card G := by
    intro n
    induction n with
    | zero =>
        rw [derivedSeries_zero, Nat.add_zero]
        exact le_of_eq (Nat.card_congr (Subgroup.topEquiv).toEquiv)
    | succ n ih =>
        have hlt : Nat.card (derivedSeries G (n + 1)) < Nat.card (derivedSeries G n) := by
          have hsub : (derivedSeries G (n + 1) : Set G) ⊂ (derivedSeries G n : Set G) := by
            rw [Set.ssubset_iff_subset_ne]
            refine ⟨derivedSeries_antitone G (Nat.le_succ n), ?_⟩
            intro hset
            apply (hstrict n).ne
            exact Subgroup.ext fun x => Iff.of_eq (congrArg (fun s : Set G => x ∈ s) hset)
          simpa using Set.Finite.card_lt_card (Set.toFinite (derivedSeries G n : Set G)) hsub
        omega
  have hcontra := hcard (Nat.card G + 1)
  omega

private lemma pslBTg1_hom_trivial_of_perfect {G A : Type} [Group G] [CommGroup A]
    [Group.IsPerfect G] (f : G →* A) : f = 1 := by
  rw [← MonoidHom.ker_eq_top_iff]
  apply top_le_iff.mp
  rw [← Group.IsPerfect.commutator_eq_top (G := G)]
  change ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ f.ker
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, mul_comm (f a) (f b),
    mul_assoc (f b) (f a) ((f a)⁻¹), mul_inv_cancel (f a), mul_one, mul_inv_cancel (f b)]

private lemma pslBTg1_pslBlock_le_pslChat {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {B : GL (Fin n) K}
    (e : Matrix (Fin n) (Fin n) K) : pslBlock B e ≤ pslChat B := by
  intro x hx
  rw [pslChat, Subgroup.mem_comap]
  show conjAut n K B (proj n K x) = proj n K x
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  have hcent : SpecialLinearGroup.toGL x ∈
      Subgroup.centralizer ({B} : Set (GL (Fin n) K)) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).1
  have hBx : B * SpecialLinearGroup.toGL x = SpecialLinearGroup.toGL x * B :=
    (Subgroup.mem_centralizer_iff.mp hcent) B (Set.mem_singleton B)
  have hmat : (B : Matrix (Fin n) (Fin n) K) *
      ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (B : Matrix (Fin n) (Fin n) K) := by
    have h := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hBx
    simpa using h
  rw [hmat, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

private lemma pslBTg1_sl_coe_inv {n : ℕ} {K : Type} [Field K]
    (x : SpecialLinearGroup (Fin n) K) :
    (((x⁻¹ : SpecialLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
      (((x : SpecialLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K)⁻¹ := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def]
  have hdet : ((x : Matrix (Fin n) (Fin n) K)).det = 1 := x.2
  rw [hdet]
  simp

private lemma pslBT_isometry_of_perfect {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    {e : Matrix (Fin n) (Fin n) K} (Y : Subgroup ↥(pslBlock B e))
    (hY : Group.IsPerfect ↥Y) :
    ∀ x : ↥Y, formAdj (RingHom.id K) G
        ((x.1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((x.1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹ := by
  intro x
  let X : ↥Y → Matrix (Fin n) (Fin n) K :=
    fun y => ((y.1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
  let d : ↥Y → Kˣ := fun y =>
    Classical.choose (S.fix ((y.1 : SpecialLinearGroup (Fin n) K))
      (pslBTg1_pslBlock_le_pslChat e y.1.2))
  have hd : ∀ y : ↥Y, formAdj (RingHom.id K) G ((X y)⁻¹) = (d y : K) • X y := by
    intro y
    have h : formAdj (RingHom.id K) G
        ((((y.1 : SpecialLinearGroup (Fin n) K))⁻¹ : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = (d y : K) • X y :=
      Classical.choose_spec (S.fix ((y.1 : SpecialLinearGroup (Fin n) K))
        (pslBTg1_pslBlock_le_pslChat e y.1.2))
    have heq : (X y)⁻¹ = ((((y.1 : SpecialLinearGroup (Fin n) K))⁻¹ :
        SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
      (pslBTg1_sl_coe_inv (y.1 : SpecialLinearGroup (Fin n) K)).symm
    rw [heq]
    simpa only [d] using h
  have hX_mul : ∀ a b : ↥Y, X (a * b) = X a * X b := fun a b => rfl
  have hne : ∀ a b : ↥Y, X a * X b ≠ 0 := by
    intro a b h0
    haveI : Nonempty (Fin n) := ⟨⟨0, by have := S.three_le; omega⟩⟩
    have hdet : (X a * X b).det = 1 := by
      rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe,
        Matrix.SpecialLinearGroup.det_coe, mul_one]
    rw [h0, Matrix.det_zero] at hdet
    exact zero_ne_one hdet
  have hdhom : ∀ a b : ↥Y, d (a * b) = d a * d b := by
    intro a b
    have hcalc : (d (a * b) : K) • (X a * X b) = ((d a : K) * (d b : K)) •
        (X a * X b) := by
      calc (d (a * b) : K) • (X a * X b)
          = (d (a * b) : K) • X (a * b) := by rw [hX_mul]
        _ = formAdj (RingHom.id K) G ((X (a * b))⁻¹) := (hd (a * b)).symm
        _ = formAdj (RingHom.id K) G (((X b)⁻¹) * ((X a)⁻¹)) := by
              rw [hX_mul, Matrix.mul_inv_rev]
        _ = formAdj (RingHom.id K) G ((X a)⁻¹) *
              formAdj (RingHom.id K) G ((X b)⁻¹) :=
              Geo.formAdj_mul (RingHom.id K) S.det_isUnit _ _
        _ = ((d a : K) • X a) * ((d b : K) • X b) := by rw [hd a, hd b]
        _ = ((d a : K) * (d b : K)) • (X a * X b) := by
              rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hinj := smul_left_injective K (hne a b)
    have hscalar : (d (a * b) : K) = (d a : K) * (d b : K) := hinj hcalc
    exact Units.ext hscalar
  let f : ↥Y →* Kˣ :=
    { toFun := d
      map_one' := by
        have h := hdhom 1 1
        have h1 : d 1 * d 1 = d 1 * 1 := by simpa using h.symm
        exact mul_left_cancel h1
      map_mul' := hdhom }
  haveI : Group.IsPerfect ↥Y := hY
  have hf : f = 1 := pslBTg1_hom_trivial_of_perfect f
  have hdx1 : d x = 1 := by
    have := congrArg (fun g : ↥Y →* Kˣ => g x) hf
    simpa [f] using this
  have hdx : formAdj (RingHom.id K) G ((X x)⁻¹) = X x := by
    rw [hd x, hdx1]
    simp
  have hGh : (G.map (RingHom.id K))ᵀ = G := by simpa using S.symm
  have h := congrArg (formAdj (RingHom.id K) G) hdx
  rw [Geo.formAdj_formAdj (RingHom.id K) (fun c => rfl) S.det_isUnit hGh] at h
  exact h.symm

private lemma pslBTg1_pslAlg_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a ∈ pslAlg B, ∀ b ∈ pslAlg B, a * b = b * a := by
  have hcommS : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  letI : CommSemiring (pslAlg B) := Algebra.adjoinCommSemiringOfComm K hcommS
  intro a ha b hb
  have h := mul_comm (⟨a, ha⟩ : pslAlg B) (⟨b, hb⟩ : pslAlg B)
  simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h

private lemma pslBTg1_star_mem_family {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    {e : Matrix (Fin n) (Fin n) K} (he : e ∈ P) :
    formAdj (RingHom.id K) G e ∈ P := by
  refine primFamily_map_mem hP (formAdj (RingHom.id K) G) ?_ ?_ ?_ ?_ (pslBTg1_pslAlg_comm B) e he
  · intro a b
    exact Geo.formAdj_add (RingHom.id K) G a b
  · intro a b
    exact Geo.formAdj_mul (RingHom.id K) S.det_isUnit a b
  · intro a ha
    exact pslGraph_star_mem S a ha
  · intro a ha
    exact Geo.formAdj_formAdj (RingHom.id K) (fun c => rfl) S.det_isUnit
      (by simpa using S.symm) a

private lemma pslBTg1_dot_mulVec_transpose {n : ℕ} {K : Type} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) :
    (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Aᵀ *ᵥ v) := by
  have hA : v ᵥ* A = Aᵀ *ᵥ v := by
    simpa using Matrix.vecMul_transpose (Aᵀ) v
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, hA, dotProduct_comm]

private lemma pslBTg1_nondegenerate {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} (hG : IsUnit G.det) {u : Fin n → K}
    (h : ∀ y : Fin n → K, u ⬝ᵥ (G *ᵥ y) = 0) : u = 0 := by
  funext i
  have hy := h (G⁻¹ *ᵥ Pi.single i 1)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG, Matrix.one_mulVec,
    dotProduct_single] at hy
  simpa using hy

private lemma pslBTg1_adjoint_dot {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} (hG : IsUnit G.det) (a : Matrix (Fin n) (Fin n) K)
    (u v : Fin n → K) :
    (a *ᵥ u) ⬝ᵥ (G *ᵥ v) =
      u ⬝ᵥ (G *ᵥ (formAdj (RingHom.id K) G a *ᵥ v)) := by
  rw [pslBTg1_dot_mulVec_transpose]
  congr 1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  unfold formAdj
  have hmap : a.map (RingHom.id K) = a := by
    ext i j
    rfl
  rw [hmap, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG,
    Matrix.one_mul]

private lemma pslBT_III_eq_one_of_isometry {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hne : formAdj (RingHom.id K) G e ≠ e)
    (x : ↥(pslBlock B e))
    (hiso : formAdj (RingHom.id K) G
        ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹) :
    x = 1 := by
  let X : Matrix (Fin n) (Fin n) K :=
    ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
  let es : Matrix (Fin n) (Fin n) K := formAdj (RingHom.id K) G e
  have heA : e ∈ pslAlg B := ((hP.1 e).mp he).1
  have hee : e * e = e := ((hP.1 e).mp he).2.1.eq
  have hesP : es ∈ P := pslBTg1_star_mem_family S P hP he
  have hesA : es ∈ pslAlg B := ((hP.1 es).mp hesP).1
  have hese : es * es = es := ((hP.1 es).mp hesP).2.1.eq
  have hees : e * es = 0 := hP.2.1 e he es hesP (fun hh => hne hh.symm)
  have hxmem := x.2
  simp only [pslBlock, glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf] at hxmem
  have hxcent := hxmem.1
  have hXfix1 : X * (1 - e) = 1 - e := by
    have h := hxmem.2
    have h' : ((SpecialLinearGroup.toGL x : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e := h
    simpa [X] using h' 
  have hxB : X * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * X := by
    have h := (Subgroup.mem_centralizer_iff.mp hxcent) B (Set.mem_singleton B)
    have h' := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h
    simpa [X] using h'.symm
  have hcommA : ∀ a ∈ pslAlg B, X * a = a * X := by
    intro a ha
    refine Algebra.adjoin_induction (p := fun a _ => X * a = a * X) ?_ ?_ ?_ ?_ ha
    · rintro a ⟨s, hs, rfl⟩
      rw [Set.mem_singleton_iff] at hs
      subst hs
      exact hxB
    · intro c
      rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul]
    · intro a b _ _ ha hb
      rw [Matrix.mul_add, Matrix.add_mul, ha, hb]
    · intro a b _ _ ha hb
      calc X * (a * b) = (X * a) * b := by rw [Matrix.mul_assoc]
        _ = (a * X) * b := by rw [ha]
        _ = a * (X * b) := by rw [Matrix.mul_assoc]
        _ = a * (b * X) := by rw [hb]
        _ = (a * b) * X := by rw [Matrix.mul_assoc]
  have hXe : X * e = e * X := hcommA e heA
  have hGdet : IsUnit X.det := by
    have h1 : X.det = 1 := by
      simpa [X] using Matrix.SpecialLinearGroup.det_coe (x : SpecialLinearGroup (Fin n) K)
    rw [h1]
    exact isUnit_one
  have hXiso : Xᵀ * G * X = G := by
    have h1 : G * X⁻¹ = Xᵀ * G := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => G * M) hiso
      have h2 : G * formAdj (RingHom.id K) G X = Xᵀ * G := by
        unfold formAdj
        have hmap : X.map (RingHom.id K) = X := by
          ext i j
          rfl
        rw [hmap, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv G S.det_isUnit, Matrix.one_mul]
      rw [h2] at h
      exact h.symm
    calc Xᵀ * G * X = (G * X⁻¹) * X := by rw [h1]
      _ = G * (X⁻¹ * X) := by rw [Matrix.mul_assoc]
      _ = G * 1 := by rw [Matrix.nonsing_inv_mul X hGdet]
      _ = G := Matrix.mul_one G
  have h_iso : ∀ a b : Fin n → K,
      (X *ᵥ a) ⬝ᵥ (G *ᵥ (X *ᵥ b)) = a ⬝ᵥ (G *ᵥ b) := by
    intro a b
    calc (X *ᵥ a) ⬝ᵥ (G *ᵥ (X *ᵥ b))
        = (X *ᵥ a) ⬝ᵥ ((G * X) *ᵥ b) := by rw [Matrix.mulVec_mulVec]
      _ = a ⬝ᵥ (Xᵀ *ᵥ ((G * X) *ᵥ b)) :=
            pslBTg1_dot_mulVec_transpose X a ((G * X) *ᵥ b)
      _ = a ⬝ᵥ ((Xᵀ * (G * X)) *ᵥ b) := by rw [Matrix.mulVec_mulVec]
      _ = a ⬝ᵥ (G *ᵥ b) := by
            rw [show Xᵀ * (G * X) = G from by rw [← Matrix.mul_assoc, hXiso]]
  have h_eV_orth : ∀ (a z : Fin n → K),
      (e *ᵥ a) ⬝ᵥ (G *ᵥ ((1 - es) *ᵥ z)) = 0 := by
    intro a z
    rw [pslBTg1_adjoint_dot S.det_isUnit e a ((1 - es) *ᵥ z)]
    have h0 : es *ᵥ ((1 - es) *ᵥ z) = 0 := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hese, sub_self,
        Matrix.zero_mulVec]
    rw [h0]
    simp
  have hXw_eq : ∀ u₀ : Fin n → K, X *ᵥ (e *ᵥ u₀) = e *ᵥ (X *ᵥ u₀) := by
    intro u₀
    rw [Matrix.mulVec_mulVec, hXe, ← Matrix.mulVec_mulVec]
  have hfix_e : ∀ u₀ : Fin n → K, X *ᵥ (e *ᵥ u₀) = e *ᵥ u₀ := by
    intro u₀
    let w : Fin n → K := e *ᵥ u₀
    have hXw : X *ᵥ w = e *ᵥ (X *ᵥ u₀) := hXw_eq u₀
    have hu : X *ᵥ w - w = 0 := by
      apply pslBTg1_nondegenerate S.det_isUnit
      intro y
      have hy_split : y = es *ᵥ y + (1 - es) *ᵥ y := by
        rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
      have h1 : (X *ᵥ w - w) ⬝ᵥ (G *ᵥ (es *ᵥ y)) = 0 := by
        have hy1fix : X *ᵥ (es *ᵥ y) = es *ᵥ y := by
          have h1fix : (1 - e) *ᵥ (es *ᵥ y) = es *ᵥ y := by
            rw [Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, hees, sub_zero]
          calc X *ᵥ (es *ᵥ y) = X *ᵥ ((1 - e) *ᵥ (es *ᵥ y)) := by rw [h1fix]
            _ = (X * (1 - e)) *ᵥ (es *ᵥ y) := by rw [Matrix.mulVec_mulVec]
            _ = (1 - e) *ᵥ (es *ᵥ y) := by rw [hXfix1]
            _ = es *ᵥ y := h1fix
        have hiso := h_iso w (es *ᵥ y)
        rw [hy1fix] at hiso
        rw [sub_dotProduct, hiso, sub_self]
      have h2 : (X *ᵥ w - w) ⬝ᵥ (G *ᵥ ((1 - es) *ᵥ y)) = 0 := by
        rw [sub_dotProduct]
        have hXw0 : (X *ᵥ w) ⬝ᵥ (G *ᵥ ((1 - es) *ᵥ y)) = 0 := by
          rw [hXw]
          exact h_eV_orth (X *ᵥ u₀) y
        have hw0 : w ⬝ᵥ (G *ᵥ ((1 - es) *ᵥ y)) = 0 := h_eV_orth u₀ y
        rw [hXw0, hw0, sub_zero]
      rw [hy_split, Matrix.mulVec_add, dotProduct_add, h1, h2, add_zero]
    exact sub_eq_zero.mp hu
  have hX1 : X = 1 := by
    refine Matrix.ext_iff_mulVec.mpr ?_
    intro v
    rw [Matrix.one_mulVec]
    have hv : e *ᵥ v + (1 - e) *ᵥ v = v := by
      rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
    rw [← hv, Matrix.mulVec_add, hfix_e v]
    have h1sub : X *ᵥ ((1 - e) *ᵥ v) = (1 - e) *ᵥ v := by
      rw [Matrix.mulVec_mulVec, hXfix1]
    rw [h1sub]
  apply Subtype.ext
  ext i j
  have h : ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    simpa [X] using hX1
  rw [h]
  simp

private lemma pslBT_III_perfect_eq_bot {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hne : formAdj (RingHom.id K) G e ≠ e)
    (Y : Subgroup ↥(pslBlock B e)) (hY : Group.IsPerfect ↥Y) : Y = ⊥ := by
  rw [← le_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hiso := pslBT_isometry_of_perfect S Y hY ⟨x, hx⟩
  have hx1 := pslBT_III_eq_one_of_isometry S P hP e he hne x hiso
  simpa using hx1

private noncomputable def pslBTg2_star {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (a : pslAlg B) : pslAlg B :=
  ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
    pslGraph_star_mem S (a : Matrix (Fin n) (Fin n) K) a.2⟩

private lemma pslBTg2_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a ∈ pslAlg B, ∀ b ∈ pslAlg B, a * b = b * a := by
  have hcommP : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  letI : CommSemiring (pslAlg B) := Algebra.adjoinCommSemiringOfComm K hcommP
  intro a ha b hb
  have h := congrArg Subtype.val (mul_comm (⟨a, ha⟩ : pslAlg B) (⟨b, hb⟩ : pslAlg B))
  simpa only [Subalgebra.coe_mul] using h

private lemma pslBTg2_star_zero {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} :
    formAdj (RingHom.id K) G (0 : Matrix (Fin n) (Fin n) K) = 0 := by
  simp [formAdj]

private lemma pslBTg2_star_one {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    pslBTg2_star S (1 : pslAlg B) = 1 := by
  apply Subtype.ext
  simp only [pslBTg2_star, Subalgebra.coe_one, formAdj_one (RingHom.id K) S.det_isUnit]

private lemma pslBTg2_star_mul {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (a b : pslAlg B) :
    pslBTg2_star S (a * b) = pslBTg2_star S b * pslBTg2_star S a := by
  apply Subtype.ext
  simp only [pslBTg2_star, Subalgebra.coe_mul, formAdj_mul (RingHom.id K) S.det_isUnit]

private lemma pslBTg2_star_add {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (a b : pslAlg B) :
    pslBTg2_star S (a + b) = pslBTg2_star S a + pslBTg2_star S b := by
  apply Subtype.ext
  simp only [pslBTg2_star, Subalgebra.coe_add, formAdj_add]

private lemma pslBTg2_star_zero' {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    pslBTg2_star S (0 : pslAlg B) = 0 := by
  apply Subtype.ext
  simp only [pslBTg2_star, Subalgebra.coe_zero, pslBTg2_star_zero]

private lemma pslBTg2_G_symm {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    Matrix.transpose (G.map (RingHom.id K)) = G := by
  ext i j
  simpa using congrFun (congrFun S.symm i) j

private lemma pslBTg2_star_invol {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (a : pslAlg B) : pslBTg2_star S (pslBTg2_star S a) = a := by
  apply Subtype.ext
  simp only [pslBTg2_star]
  exact formAdj_formAdj (RingHom.id K) (fun x => rfl) S.det_isUnit (pslBTg2_G_symm S)
    (a : Matrix (Fin n) (Fin n) K)

private lemma pslBTg2_star_algebraMap {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (c : K) :
    pslBTg2_star S (algebraMap K (pslAlg B) c) = algebraMap K (pslAlg B) c := by
  apply Subtype.ext
  simp only [pslBTg2_star, Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul,
    Subalgebra.coe_one, formAdj_smul, formAdj_one (RingHom.id K) S.det_isUnit,
    RingHom.id_apply]

private lemma pslBTg2_factor {A B E : Type*} [Ring A] [Ring B] [Ring E]
    (π : A →+* B) (hπ : Function.Surjective π) (ρ : A →+* E)
    (hker : ∀ a, π a = 0 → ρ a = 0) :
    ∃ φ : B →+* E, ∀ a, φ (π a) = ρ a :=
  ⟨RingHom.liftOfSurjective π hπ ⟨ρ, fun a ha => hker a ha⟩,
    fun a => RingHom.liftOfSurjective_comp_apply π hπ ⟨ρ, fun a ha => hker a ha⟩ a⟩

private lemma pslBT_tau {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    {e : Matrix (Fin n) (Fin n) K} (he : e ∈ pslAlg B)
    (hstar : formAdj (RingHom.id K) G e = e)
    {F : Type} [Field F] [Algebra K F] (π : pslAlg B →ₐ[K] F) (hπ : Function.Surjective π)
    (hker : ∀ a : pslAlg B, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e = 0) :
    ∃ τ : F ≃+* F, (∀ x, τ (τ x) = x) ∧
      (∀ c : K, τ (algebraMap K F c) = algebraMap K F c) ∧
      ∀ a : pslAlg B, τ (π a) =
        π ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
          pslGraph_star_mem S (a : Matrix (Fin n) (Fin n) K) a.2⟩ := by
  let ρ : pslAlg B →+* F :=
    { toFun := fun a => π (pslBTg2_star S a)
      map_one' := by rw [pslBTg2_star_one S, map_one]
      map_mul' := by
        intro a b
        rw [pslBTg2_star_mul S a b, map_mul, mul_comm]
      map_zero' := by rw [pslBTg2_star_zero' S, map_zero]
      map_add' := by
        intro a b
        rw [pslBTg2_star_add S a b, map_add] }
  have hkerρ : ∀ a : pslAlg B, π.toRingHom a = 0 → ρ a = 0 := by
    intro a h0
    have hae : (a : Matrix (Fin n) (Fin n) K) * e = 0 := (hker a).mp h0
    have h1 : formAdj (RingHom.id K) G ((a : Matrix (Fin n) (Fin n) K) * e) = 0 := by
      rw [hae, pslBTg2_star_zero]
    rw [formAdj_mul (RingHom.id K) S.det_isUnit, hstar] at h1
    have h2 : (pslBTg2_star S a : Matrix (Fin n) (Fin n) K) * e = 0 := by
      rw [pslBTg2_comm B (pslBTg2_star S a) (pslBTg2_star S a).2 e he]
      exact h1
    exact (hker (pslBTg2_star S a)).mpr h2
  obtain ⟨φ, hφ⟩ := pslBTg2_factor π.toRingHom hπ ρ hkerρ
  have hφ' : ∀ a : pslAlg B, φ (π a) = π (pslBTg2_star S a) := fun a => hφ a
  have hφφa : ∀ a : pslAlg B, φ (φ (π a)) = π a := by
    intro a
    rw [hφ' a, hφ' (pslBTg2_star S a), pslBTg2_star_invol S a]
  have hφφ : ∀ x : F, φ (φ x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := hπ x
    exact hφφa a
  refine ⟨RingEquiv.ofBijective φ (Function.Involutive.bijective hφφ), ?_, ?_, ?_⟩
  · intro x
    simpa only [RingEquiv.ofBijective_apply] using hφφ x
  · intro c
    rw [RingEquiv.ofBijective_apply, ← AlgHom.commutes π c, hφ' (algebraMap K (pslAlg B) c),
      pslBTg2_star_algebraMap S c]
  · intro a
    rw [RingEquiv.ofBijective_apply]
    exact hφ' a

private lemma pslBTg3_comm_alg {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    (x : GL (Fin n) K)
    (hxB : (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K)) :
    ∀ a ∈ pslAlg B, (x : Matrix (Fin n) (Fin n) K) * a =
      a * (x : Matrix (Fin n) (Fin n) K) := by
  intro a ha
  refine Algebra.adjoin_induction (p := fun a _ =>
    (x : Matrix (Fin n) (Fin n) K) * a = a * (x : Matrix (Fin n) (Fin n) K)) ?_ ?_ ?_ ?_ ha
  · rintro y ⟨u, hu, rfl⟩
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact hxB
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  · intro a b _ _ ha hb
    rw [mul_add, add_mul, ha, hb]
  · intro a b _ _ ha hb
    calc (x : Matrix (Fin n) (Fin n) K) * (a * b)
        = ((x : Matrix (Fin n) (Fin n) K) * a) * b := by rw [mul_assoc]
      _ = (a * (x : Matrix (Fin n) (Fin n) K)) * b := by rw [ha]
      _ = a * ((x : Matrix (Fin n) (Fin n) K) * b) := by rw [mul_assoc]
      _ = a * (b * (x : Matrix (Fin n) (Fin n) K)) := by rw [hb]
      _ = (a * b) * (x : Matrix (Fin n) (Fin n) K) := by rw [mul_assoc]

private lemma pslBTg3_restrict_aux {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    {e : Matrix (Fin n) (Fin n) K} (heB : e ∈ pslAlg B)
    {F : Type} [Field F] [Algebra K F] (π : pslAlg B →ₐ[K] F) (hπ : Function.Surjective π)
    [Module F (LinearMap.range e.mulVecLin)]
    (hact : ∀ (a : pslAlg B) (w : LinearMap.range e.mulVecLin),
      ((π a • w : LinearMap.range e.mulVecLin) : Fin n → K) =
        (a : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K))
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hψw : ∀ (g : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin)
      (w : LinearMap.range e.mulVecLin),
      (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
        ((g w : LinearMap.range e.mulVecLin) : Fin n → K))
    (hψfix : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e)
    (x : GL (Fin n) K) (hxB : (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K))
    (hxfix : (x : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e) :
    ∃ g : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin, ψ g = x := by
  have hxcomm := pslBTg3_comm_alg x hxB
  have hxe : (x : Matrix (Fin n) (Fin n) K) * e = e * (x : Matrix (Fin n) (Fin n) K) :=
    hxcomm e heB
  have hmem_of : ∀ (y : GL (Fin n) K), (y : Matrix (Fin n) (Fin n) K) * e =
      e * (y : Matrix (Fin n) (Fin n) K) → ∀ w : LinearMap.range e.mulVecLin,
      (y : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) ∈ LinearMap.range e.mulVecLin := by
    intro y hy w
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp w.2
    rw [Matrix.mulVecLin_apply] at hu
    refine ⟨(y : Matrix (Fin n) (Fin n) K) *ᵥ u, ?_⟩
    show e *ᵥ ((y : Matrix (Fin n) (Fin n) K) *ᵥ u) =
      (y : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K)
    rw [← hu, Matrix.mulVec_mulVec, ← hy, Matrix.mulVec_mulVec]
  let gLin : LinearMap.range e.mulVecLin →ₗ[F] LinearMap.range e.mulVecLin :=
    { toFun := fun w => ⟨(x : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K), hmem_of x hxe w⟩
      map_add' := by
        intro w1 w2
        apply Subtype.ext
        show (x : Matrix (Fin n) (Fin n) K) *ᵥ ((w1 : Fin n → K) + (w2 : Fin n → K)) =
          (x : Matrix (Fin n) (Fin n) K) *ᵥ (w1 : Fin n → K) +
            (x : Matrix (Fin n) (Fin n) K) *ᵥ (w2 : Fin n → K)
        rw [Matrix.mulVec_add]
      map_smul' := by
        intro c w
        obtain ⟨a, rfl⟩ := hπ c
        apply Subtype.ext
        show (x : Matrix (Fin n) (Fin n) K) *ᵥ
            (((π a • w : LinearMap.range e.mulVecLin)) : Fin n → K) =
          (((π a • (⟨(x : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K),
            hmem_of x hxe w⟩ : LinearMap.range e.mulVecLin)) : LinearMap.range e.mulVecLin) :
              Fin n → K)
        rw [hact a w, hact a ⟨(x : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K),
          hmem_of x hxe w⟩]
        show (x : Matrix (Fin n) (Fin n) K) *ᵥ ((a : Matrix (Fin n) (Fin n) K) *ᵥ
            (w : Fin n → K)) = (a : Matrix (Fin n) (Fin n) K) *ᵥ
              ((x : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K))
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          hxcomm (a : Matrix (Fin n) (Fin n) K) a.2] }
  have hgLin_inj : Function.Injective gLin := by
    intro w1 w2 h
    apply Subtype.ext
    have h' : (x : Matrix (Fin n) (Fin n) K) *ᵥ (w1 : Fin n → K) =
        (x : Matrix (Fin n) (Fin n) K) *ᵥ (w2 : Fin n → K) :=
      congrArg (fun w : LinearMap.range e.mulVecLin => (w : Fin n → K)) h
    have h2 := congrArg (fun v : Fin n → K =>
      ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) h'
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.one_mulVec] using h2
  have hxe_inv : ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * e =
      e * ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    let a : Matrix (Fin n) (Fin n) K := ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    let b : Matrix (Fin n) (Fin n) K := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    have hab1 : a * b = 1 := by
      show ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hab2 : b * a = 1 := by
      show ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    change a * e = e * a
    calc a * e
        = (a * e) * 1 := (mul_one _).symm
      _ = (a * e) * (b * a) := by rw [hab2]
      _ = ((a * e) * b) * a := (mul_assoc (a * e) b a).symm
      _ = (a * (e * b)) * a := congrArg (fun z => z * a) (mul_assoc a e b)
      _ = (a * (b * e)) * a := congrArg (fun z => (a * z) * a) hxe.symm
      _ = ((a * b) * e) * a := congrArg (fun z => z * a) (mul_assoc a b e).symm
      _ = e * a := by rw [hab1, one_mul]
  have hgLin_surj : Function.Surjective gLin := by
    intro u
    refine ⟨⟨((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (u : Fin n → K),
      hmem_of x⁻¹ hxe_inv u⟩, ?_⟩
    apply Subtype.ext
    show (x : Matrix (Fin n) (Fin n) K) *ᵥ
        (((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (u : Fin n → K)) =
      (u : Fin n → K)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  refine ⟨LinearEquiv.ofBijective gLin ⟨hgLin_inj, hgLin_surj⟩, ?_⟩
  apply Units.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  have hdecomp : e *ᵥ v + (1 - e) *ᵥ v = v := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  have h1 : (ψ (LinearEquiv.ofBijective gLin ⟨hgLin_inj, hgLin_surj⟩) :
        Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ v) =
      (x : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ v) :=
    hψw (LinearEquiv.ofBijective gLin ⟨hgLin_inj, hgLin_surj⟩)
      ⟨e *ᵥ v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩
  have h2 : (ψ (LinearEquiv.ofBijective gLin ⟨hgLin_inj, hgLin_surj⟩) :
        Matrix (Fin n) (Fin n) K) *ᵥ ((1 - e) *ᵥ v) = (1 - e) *ᵥ v := by
    rw [Matrix.mulVec_mulVec, hψfix]
  have h3 : (x : Matrix (Fin n) (Fin n) K) *ᵥ ((1 - e) *ᵥ v) = (1 - e) *ᵥ v := by
    rw [Matrix.mulVec_mulVec, hxfix]
  calc (ψ (LinearEquiv.ofBijective gLin ⟨hgLin_inj, hgLin_surj⟩) :
        Matrix (Fin n) (Fin n) K) *ᵥ v
      = (ψ (LinearEquiv.ofBijective gLin ⟨hgLin_inj, hgLin_surj⟩) :
          Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ v + (1 - e) *ᵥ v) := by rw [hdecomp]
    _ = (ψ (LinearEquiv.ofBijective gLin ⟨hgLin_inj, hgLin_surj⟩) :
          Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ v) +
        (ψ (LinearEquiv.ofBijective gLin ⟨hgLin_inj, hgLin_surj⟩) :
          Matrix (Fin n) (Fin n) K) *ᵥ ((1 - e) *ᵥ v) := by rw [Matrix.mulVec_add]
    _ = (x : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ v) + (1 - e) *ᵥ v := by rw [h1, h2]
    _ = (x : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ v) +
        (x : Matrix (Fin n) (Fin n) K) *ᵥ ((1 - e) *ᵥ v) := by rw [h3]
    _ = (x : Matrix (Fin n) (Fin n) K) *ᵥ (e *ᵥ v + (1 - e) *ᵥ v) := by rw [Matrix.mulVec_add]
    _ = (x : Matrix (Fin n) (Fin n) K) *ᵥ v := by rw [hdecomp]

private lemma pslBTg3_gl_solvable_one {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h : Module.finrank F V = 1) :
    Group.IsSolvable (V ≃ₗ[F] V) := by
  apply Group.isSolvable_of_comm
  intro f g
  apply LinearEquiv.ext
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hspan : Submodule.span F {x} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_singleton hx, h]
    have hgx : g x ∈ Submodule.span F {x} := by rw [hspan]; trivial
    have hfx : f x ∈ Submodule.span F {x} := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgx
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hfx
    have hc' : g x = c • x := hc.symm
    have hd' : f x = d • x := hd.symm
    show f (g x) = g (f x)
    calc f (g x) = f (c • x) := by rw [hc']
      _ = c • f x := by rw [map_smul]
      _ = c • (d • x) := by rw [hd']
      _ = (c * d) • x := by rw [smul_smul]
      _ = (d * c) • x := by rw [mul_comm]
      _ = d • (c • x) := by rw [smul_smul]
      _ = d • g x := by rw [hc']
      _ = g (d • x) := by rw [map_smul]
      _ = g (f x) := by rw [hd']

private lemma pslBTg3_gl_solvable_two {F V : Type} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [Fintype V] (h : Module.finrank F V = 2)
    (hc : Nat.card F = 2) : Group.IsSolvable (V ≃ₗ[F] V) := by
  letI : Fintype F := Fintype.ofFinite F
  letI : Module.Free F V := Module.Free.of_divisionRing F V
  have hcardV : Fintype.card V = 4 := by
    let b := Module.finBasis F V
    have hb : Fintype.card V = Fintype.card (Fin (Module.finrank F V) → F) :=
      Fintype.card_congr b.equivFun.toEquiv
    rw [h] at hb
    rw [hb, Fintype.card_fun]
    have hF : Fintype.card F = 2 := by rwa [← Nat.card_eq_fintype_card]
    rw [hF]; norm_num
  let act : (V ≃ₗ[F] V) →* Equiv.Perm V :=
    { toFun := fun g => Equiv.ofBijective (g : V →ₗ[F] V) g.bijective
      map_one' := by ext v; rfl
      map_mul' := by intro a b; ext v; rfl }
  have hactinj : Function.Injective act := by
    intro a b hab
    apply LinearEquiv.ext
    intro v
    have h2 : (act a : V → V) = (act b : V → V) :=
      congrArg (fun e : Equiv.Perm V => (e : V → V)) hab
    simpa [act] using congrFun h2 v
  haveI : Group.IsSolvable (Equiv.Perm V) :=
    Equiv.Perm.isSolvable (α := V) (by rw [Nat.card_eq_fintype_card, hcardV])
  exact solvable_of_solvable_injective hactinj

private lemma pslBTg3_hom_trivial_of_perfect {G A : Type} [Group G] [CommGroup A]
    [Group.IsPerfect G] (f : G →* A) : f = 1 := by
  rw [← MonoidHom.ker_eq_top_iff]
  apply top_le_iff.mp
  rw [← Group.IsPerfect.commutator_eq_top (G := G)]
  change ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ f.ker
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, mul_comm (f a) (f b),
    mul_assoc (f b) (f a) ((f a)⁻¹), mul_inv_cancel (f a), mul_one, mul_inv_cancel (f b)]

private lemma pslBTg3_perfect {F : Type} [Field F] [Finite F] [CharP F 2]
    (k : ℕ) (hk : 2 ≤ k) (hnot : ¬ (k = 2 ∧ Nat.card F = 2)) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin k) F) := by
  refine CFSG.LinearGroups.special_linear_isPerfect hk ?_
  by_cases hk3 : 3 ≤ k
  · exact Or.inl hk3
  · right
    have hk2 : k = 2 := by omega
    haveI : Fintype F := Fintype.ofFinite F
    have hcard_ne : Nat.card F ≠ 2 := fun h => hnot ⟨hk2, h⟩
    have h2 : 2 ≤ Nat.card F := by
      have := Fintype.one_lt_card (α := F)
      rw [Nat.card_eq_fintype_card]
      omega
    have hcard_ne3 : Nat.card F ≠ 3 := by
      intro h3
      have h0 : (Nat.card F : F) = 0 := by
        rw [Nat.card_eq_fintype_card]
        exact Nat.cast_card_eq_zero F
      rw [h3] at h0
      exact (by norm_num : ¬ 2 ∣ 3) ((CharP.cast_eq_zero_iff F 2 3).mp h0)
    have hcard_ge : 4 ≤ Nat.card F := by omega
    have h4 : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact hcard_ge
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := Finset.univ) h4
    exact ⟨s, hs⟩

private lemma pslBTg3_SL_embed {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (k : ℕ),
      Nat.card F = Nat.card K ^ blockDegree (pslAlg B) e ∧
      Matrix.rank e = blockDegree (pslAlg B) e * k ∧ 0 < k ∧
      (Group.IsPerfect (Matrix.SpecialLinearGroup (Fin k) F) →
        ∃ φ : Matrix.SpecialLinearGroup (Fin k) F →* ↥(pslBlock B e),
          Function.Injective φ) := by
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, -, -, hdim, hcard, -, hrank, hpos, hψinj,
    -, hψfix, -, hψB⟩ := exists_blockEmbed S.odd rfl ((hP.1 e).1 he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Module F (LinearMap.range e.mulVecLin) := hM
  letI : IsScalarTower K F (LinearMap.range e.mulVecLin) := hT
  refine ⟨F, hFld, hFin, hChar, Module.finrank F (LinearMap.range e.mulVecLin), hcard, ?_, hpos,
    ?_⟩
  · rw [hrank, hdim]
  · intro hperf
    haveI : Module.Finite K (LinearMap.range e.mulVecLin) := Module.Finite.of_finite
    haveI : Module.Finite F (LinearMap.range e.mulVecLin) :=
      Module.Finite.of_restrictScalars_finite K F (LinearMap.range e.mulVecLin)
    let b : Module.Basis (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F
        (LinearMap.range e.mulVecLin) := Module.finBasis F (LinearMap.range e.mulVecLin)
    let A0 : Type := Fin (Module.finrank F (LinearMap.range e.mulVecLin)) → F
    let iotaBar : Matrix.SpecialLinearGroup
        (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →* (A0 ≃ₗ[F] A0) :=
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv F A0).toMonoidHom).comp
        ((Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp (Matrix.SpecialLinearGroup.toGL))
    have hIotaBar : Function.Injective iotaBar := by
      intro g h hgh
      exact SpecialLinearGroup.toGL_injective
        (Matrix.GeneralLinearGroup.toLin.injective
          ((LinearMap.GeneralLinearGroup.generalLinearEquiv F A0).injective hgh))
    let c : A0 ≃ₗ[F] LinearMap.range e.mulVecLin := b.equivFun.symm
    let conjC : (A0 ≃ₗ[F] A0) ≃*
        (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) :=
      { toFun := fun e => c.symm.trans (e.trans c)
        invFun := fun e => c.trans (e.trans c.symm)
        left_inv := fun e => by
          apply LinearEquiv.ext
          intro w
          simp [LinearEquiv.trans_apply]
        right_inv := fun e => by
          apply LinearEquiv.ext
          intro w
          simp [LinearEquiv.trans_apply]
        map_mul' := fun e f => by
          apply LinearEquiv.ext
          intro w
          simp [LinearEquiv.trans_apply, map_mul] }
    let iota : Matrix.SpecialLinearGroup
        (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →*
        (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) :=
      conjC.toMonoidHom.comp iotaBar
    have hIo : Function.Injective iota := conjC.injective.comp hIotaBar
    let A : Matrix.SpecialLinearGroup (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →*
        GL (Fin n) K := ψ.comp iota
    haveI : Group.IsPerfect
        (Matrix.SpecialLinearGroup (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F) :=
      hperf
    have htriv : (Matrix.GeneralLinearGroup.det.comp A) = 1 :=
      pslBTg3_hom_trivial_of_perfect (Matrix.GeneralLinearGroup.det.comp A)
    have hdet : ∀ g : Matrix.SpecialLinearGroup
        (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F,
        (A g : Matrix (Fin n) (Fin n) K).det = 1 := by
      intro g
      have h := congrArg (fun f : Matrix.SpecialLinearGroup
          (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →* Kˣ => f g) htriv
      simpa using congrArg Units.val h
    let slgHom : Matrix.SpecialLinearGroup
        (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →*
        Matrix.SpecialLinearGroup (Fin n) K :=
      { toFun := fun g => ⟨(A g : Matrix (Fin n) (Fin n) K), hdet g⟩
        map_one' := by
          apply Subtype.ext
          rw [Matrix.SpecialLinearGroup.coe_one]
          exact congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) (map_one A)
        map_mul' := fun g h => by
          apply Subtype.ext
          exact congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K))
            (map_mul A g h) }
    have hmemP : ∀ g, slgHom g ∈ pslBlock B e := by
      intro g
      refine Subgroup.mem_comap.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · rw [Subgroup.mem_centralizer_iff]
        intro hB hBhB
        rw [Set.mem_singleton_iff] at hBhB
        subst hB
        apply Units.ext
        rw [Units.val_mul, Units.val_mul]
        exact (hψB (iota g)).symm
      · exact hψfix (iota g)
    let φ : Matrix.SpecialLinearGroup
        (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →* ↥(pslBlock B e) :=
      { toFun := fun g => ⟨slgHom g, hmemP g⟩
        map_one' := Subtype.ext (map_one slgHom)
        map_mul' := fun g h => Subtype.ext (map_mul slgHom g h) }
    refine ⟨φ, ?_⟩
    intro g h hgh
    have h1 : slgHom g = slgHom h := congrArg Subtype.val hgh
    have h2 : A g = A h := Units.ext
      (congrArg (fun x : Matrix.SpecialLinearGroup (Fin n) K =>
        (x : Matrix (Fin n) (Fin n) K)) h1)
    exact hIo (hψinj h2)

private lemma pslBTg3_small_solvable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hsmall : Matrix.rank e = blockDegree (pslAlg B) e ∨
      (Matrix.rank e = 2 * blockDegree (pslAlg B) e ∧
        Nat.card K ^ blockDegree (pslAlg B) e = 2)) :
    Group.IsSolvable ↥(pslBlock B e) := by
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, hact,
    hrank, hpos, hψinj, hψw, hψfix, hψe, hψB⟩ := exists_blockEmbed S.odd rfl ((hP.1 e).1 he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Module F (LinearMap.range e.mulVecLin) := hM
  letI : IsScalarTower K F (LinearMap.range e.mulVecLin) := hT
  letI : Finite F := hFin
  letI : CharP F 2 := hChar
  haveI : Module.Finite K F := Module.Finite.of_finite
  haveI : Module.Finite K (LinearMap.range e.mulVecLin) := Module.Finite.of_finite
  haveI : Module.Finite F (LinearMap.range e.mulVecLin) :=
    Module.Finite.of_restrictScalars_finite K F (LinearMap.range e.mulVecLin)
  haveI : Fintype (LinearMap.range e.mulVecLin) := Fintype.ofFinite _
  have hdpos : 0 < Module.finrank K F := Module.finrank_pos
  have hk : Module.finrank F (LinearMap.range e.mulVecLin) = 1 ∨
      (Module.finrank F (LinearMap.range e.mulVecLin) = 2 ∧ Nat.card F = 2) := by
    rcases hsmall with h | ⟨h2, hK⟩
    · left
      refine Nat.eq_of_mul_eq_mul_left hdpos ?_
      rw [mul_one, ← hrank, h, hdim]
    · right
      refine ⟨Nat.eq_of_mul_eq_mul_left hdpos ?_, ?_⟩
      · rw [← hrank, h2, hdim, mul_comm]
      · rw [hcard, hK]
  have hφ : ∀ x : ↥(pslBlock B e),
      ∃ g : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin,
        ψ g = SpecialLinearGroup.toGL (x : SpecialLinearGroup (Fin n) K) := by
    intro x
    have hxmem : SpecialLinearGroup.toGL (x : SpecialLinearGroup (Fin n) K) ∈
        Subgroup.centralizer ({B} : Set (GL (Fin n) K)) ⊓ glFixing (1 - e) :=
      Subgroup.mem_comap.mp x.2
    obtain ⟨hcent, hfix⟩ := Subgroup.mem_inf.mp hxmem
    have hxB : ((SpecialLinearGroup.toGL (x : SpecialLinearGroup (Fin n) K) :
          GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) *
          ((SpecialLinearGroup.toGL (x : SpecialLinearGroup (Fin n) K) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) := by
      have h := (Subgroup.mem_centralizer_iff.mp hcent B (Set.mem_singleton B)).symm
      simpa using congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) h
    have hxfix : ((SpecialLinearGroup.toGL (x : SpecialLinearGroup (Fin n) K) :
          GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e := hfix
    exact pslBTg3_restrict_aux ((hP.1 e).1 he).1
      π hπ hact ψ hψw hψfix (SpecialLinearGroup.toGL (x : SpecialLinearGroup (Fin n) K))
        hxB hxfix
  let χ : ↥(pslBlock B e) →*
      (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) :=
    { toFun := fun x => Classical.choose (hφ x)
      map_one' := by
        apply hψinj
        simpa using Classical.choose_spec (hφ 1)
      map_mul' := by
        intro x y
        apply hψinj
        simp only [map_mul]
        rw [Classical.choose_spec (hφ (x * y)), Classical.choose_spec (hφ x),
          Classical.choose_spec (hφ y), Subgroup.coe_mul, map_mul] }
  have hχinj : Function.Injective χ := by
    intro x y h
    apply Subtype.ext
    apply SpecialLinearGroup.toGL_injective
    calc SpecialLinearGroup.toGL (x : SpecialLinearGroup (Fin n) K)
        = ψ (Classical.choose (hφ x)) := (Classical.choose_spec (hφ x)).symm
      _ = ψ (Classical.choose (hφ y)) := by
            have hg := congrArg (fun g => ψ g) h
            simpa [χ] using hg
      _ = SpecialLinearGroup.toGL (y : SpecialLinearGroup (Fin n) K) :=
            Classical.choose_spec (hφ y)
  haveI : Group.IsSolvable
      (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) := by
    rcases hk with h1 | ⟨h2, hc2⟩
    · exact pslBTg3_gl_solvable_one h1
    · exact pslBTg3_gl_solvable_two h2 hc2
  exact solvable_of_solvable_injective hχinj

private lemma pslBT_nonsolvable_params {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P)
    (hns : ¬ Group.IsSolvable ↥(pslBlock B e)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (k : ℕ),
      Nat.card F = Nat.card K ^ blockDegree (pslAlg B) e ∧
      Matrix.rank e = blockDegree (pslAlg B) e * k ∧
      2 ≤ k ∧ ¬ (k = 2 ∧ Nat.card F = 2) ∧
      ∃ φ : Matrix.SpecialLinearGroup (Fin k) F →* ↥(pslBlock B e), Function.Injective φ := by
  obtain ⟨F, hFld, hFin, hChar, k, hcard, hrank, hkpos, hφ⟩ :=
    pslBTg3_SL_embed S P hP e he
  letI : Field F := hFld
  letI : Finite F := hFin
  letI : CharP F 2 := hChar
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k = 1 := by omega
    have hsmall : Matrix.rank e = blockDegree (pslAlg B) e ∨
        (Matrix.rank e = 2 * blockDegree (pslAlg B) e ∧
          Nat.card K ^ blockDegree (pslAlg B) e = 2) :=
      Or.inl (by rw [hrank, hk1, mul_one])
    exact hns (pslBTg3_small_solvable S P hP e he hsmall)
  have hnot : ¬ (k = 2 ∧ Nat.card F = 2) := by
    rintro ⟨hk, hF2⟩
    have hsmall : Matrix.rank e = blockDegree (pslAlg B) e ∨
        (Matrix.rank e = 2 * blockDegree (pslAlg B) e ∧
          Nat.card K ^ blockDegree (pslAlg B) e = 2) :=
      Or.inr ⟨by rw [hrank, hk]; ring, by rw [← hcard]; exact hF2⟩
    exact hns (pslBTg3_small_solvable S P hP e he hsmall)
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin k) F) :=
    pslBTg3_perfect k hk2 hnot
  obtain ⟨φ, hφinj⟩ := hφ hperf
  exact ⟨F, hFld, hFin, hChar, k, hcard, hrank, hk2, hnot, φ, hφinj⟩

private lemma pslBT_isUnitaryInvolution {F : Type} [Field F] [Finite F]
    (τ : F ≃+* F) (hττ : ∀ x, τ (τ x) = x) (hne : ∃ x, τ x ≠ x) :
    CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution τ := by
  have hτ2 : τ * τ = 1 := by
    ext x
    exact hττ x
  have hτ1 : τ ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    intro h
    exact hx (by simpa using congrArg (fun e : F ≃+* F => e x) h)
  exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALang.isUnitaryInvolution_of_involution
    hτ1 hτ2

private lemma pslBT_traceTransfer {K F V : Type} [Field K] [Finite K] [Field F] [Finite F]
    [Algebra K F] [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower K F V]
    (σ : K →+* K) (τ : F ≃+* F)
    (hσσ : ∀ c, σ (σ c) = c) (hττ : ∀ x, τ (τ x) = x)
    (hτσ : ∀ c : K, τ (algebraMap K F c) = algebraMap K F (σ c))
    (hK : V → V → K)
    (hKaddL : ∀ x y z, hK (x + y) z = hK x z + hK y z)
    (hKaddR : ∀ x y z, hK x (y + z) = hK x y + hK x z)
    (hKsmulR : ∀ (c : K) x y, hK x (c • y) = c * hK x y)
    (hKherm : ∀ x y, hK x y = σ (hK y x))
    (hKnd : ∀ x, (∀ y, hK x y = 0) → x = 0)
    (hKF : ∀ (a : F) x y, hK (a • x) y = hK x (τ a • y)) :
    ∃ H : V → V → F,
      (∀ x y z, H (x + y) z = H x z + H y z) ∧ (∀ x y z, H x (y + z) = H x y + H x z) ∧
      (∀ (a : F) x y, H (a • x) y = τ a * H x y) ∧ (∀ (a : F) x y, H x (a • y) = a * H x y) ∧
      (∀ x y, H x y = τ (H y x)) ∧ (∀ x, (∀ y, H x y = 0) → x = 0) ∧
      (∀ x y, hK x y = Algebra.trace K F (H x y)) :=
  exists_hermTransfer σ τ hσσ hττ hτσ hK hKaddL hKaddR hKsmulR hKherm hKnd hKF

private def pslBTg4_h {n : ℕ} {K : Type} [Field K] (G : Matrix (Fin n) (Fin n) K)
    (u v : Fin n → K) : K :=
  u ⬝ᵥ G *ᵥ v

private lemma pslBTg4_hom_trivial_of_perfect {G A : Type} [Group G] [CommGroup A]
    [Group.IsPerfect G] (f : G →* A) : f = 1 := by
  rw [← MonoidHom.ker_eq_top_iff]
  apply top_le_iff.mp
  rw [← Group.IsPerfect.commutator_eq_top (G := G)]
  change ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ f.ker
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, mul_comm (f a) (f b),
    mul_assoc (f b) (f a) ((f a)⁻¹), mul_inv_cancel (f a), mul_one, mul_inv_cancel (f b)]

private lemma pslBTg4_transpose_mul_of_formAdj_inv {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} (hG : IsUnit G.det) (X : GL (Fin n) K)
    (hX : formAdj (RingHom.id K) G (X : Matrix (Fin n) (Fin n) K) =
      ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    Matrix.transpose (X : Matrix (Fin n) (Fin n) K) * G * (X : Matrix (Fin n) (Fin n) K) = G := by
  have hmap : (X : Matrix (Fin n) (Fin n) K).map (RingHom.id K) =
      (X : Matrix (Fin n) (Fin n) K) := by
    ext i j
    rfl
  rw [formAdj, hmap] at hX
  have h1 : Matrix.transpose (X : Matrix (Fin n) (Fin n) K) * G =
      G * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    calc Matrix.transpose (X : Matrix (Fin n) (Fin n) K) * G
        = (G * G⁻¹) * (Matrix.transpose (X : Matrix (Fin n) (Fin n) K) * G) := by
          rw [Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
      _ = G * (G⁻¹ * Matrix.transpose (X : Matrix (Fin n) (Fin n) K) * G) := by
          simp only [Matrix.mul_assoc]
      _ = G * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hX]
  calc Matrix.transpose (X : Matrix (Fin n) (Fin n) K) * G * (X : Matrix (Fin n) (Fin n) K)
      = (G * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          (X : Matrix (Fin n) (Fin n) K) := by rw [h1]
    _ = G * 1 := by rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    _ = G := Matrix.mul_one G

private lemma pslBTg4_h_preserved {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} {X : Matrix (Fin n) (Fin n) K}
    (hX : Matrix.transpose X * G * X = G) (u v : Fin n → K) :
    pslBTg4_h G (X *ᵥ u) (X *ᵥ v) = pslBTg4_h G u v := by
  unfold pslBTg4_h
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose X u,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hX, Matrix.dotProduct_mulVec]

private lemma pslBTg4_trace_ext {K F : Type} [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F] {z z' : F}
    (h : ∀ c : F, Algebra.trace K F (c * z) = Algebra.trace K F (c * z')) : z = z' := by
  have hzero : ∀ c : F, Algebra.trace K F (c * (z - z')) = 0 := by
    intro c
    rw [mul_sub, map_sub, h c, sub_self]
  have hz : z - z' = 0 := by
    let D : F ≃ₗ[K] Module.Dual K F :=
      (Algebra.traceForm K F).toDual (traceForm_nondegenerate K F)
    have hD : D (z - z') = 0 := by
      ext c
      rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply, mul_comm]
      exact hzero c
    exact D.injective (by rw [hD, map_zero])
  exact sub_eq_zero.mp hz

private lemma pslBTg4_H_preserved {K F V : Type} [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F] [AddCommGroup V] [Module F V]
    (τ : F ≃+* F) (hK : V → V → K) (H : V → V → F)
    (htrace : ∀ x y, hK x y = Algebra.trace K F (H x y))
    (hHsmulL : ∀ (a : F) x y, H (a • x) y = τ a * H x y)
    (hHsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (hKF : ∀ (a : F) x y, hK (a • x) y = hK x (τ a • y))
    (g : V ≃ₗ[F] V) (hpres : ∀ x y, hK (g x) (g y) = hK x y) :
    ∀ x y, H (g x) (g y) = H x y := by
  intro x y
  apply pslBTg4_trace_ext (K := K) (F := F)
  intro c
  obtain ⟨a, rfl⟩ := τ.surjective c
  calc Algebra.trace K F (τ a * H (g x) (g y))
      = Algebra.trace K F (H (a • g x) (g y)) := by rw [hHsmulL]
    _ = hK (a • g x) (g y) := (htrace (a • g x) (g y)).symm
    _ = hK (g (a • x)) (g y) := by rw [map_smul]
    _ = hK (a • x) y := hpres (a • x) y
    _ = hK x (τ a • y) := hKF a x y
    _ = Algebra.trace K F (H x (τ a • y)) := htrace x (τ a • y)
    _ = Algebra.trace K F (τ a * H x y) := by rw [hHsmulR]

private lemma pslBTg4_range_perfect {G H : Type} [Group G] [Group H] (f : G →* H)
    [Group.IsPerfect G] : Group.IsPerfect ↥(MonoidHom.range f) :=
  Group.IsPerfect.range f

private lemma pslBTg4_copy_contra {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    {e : Matrix (Fin n) (Fin n) K}
    {F : Type} [Field F] [Algebra K F]
    [Module F (LinearMap.range e.mulVecLin)]
    [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (ψ : (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) →* GL (Fin n) K)
    (hψw : ∀ (g : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin)
      (w : LinearMap.range e.mulVecLin),
      (ψ g : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) =
        ((g w : LinearMap.range e.mulVecLin) : Fin n → K))
    (hψfix : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e)
    (hψB : ∀ g, (ψ g : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * (ψ g : Matrix (Fin n) (Fin n) K))
    (hperf : Group.IsPerfect (Matrix.SpecialLinearGroup
      (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F))
    (τ : F ≃+* F)
    (H : LinearMap.range e.mulVecLin → LinearMap.range e.mulVecLin → F)
    (htrace : ∀ (x y : LinearMap.range e.mulVecLin), pslBTg4_h G (x : Fin n → K) (y : Fin n → K) =
      Algebra.trace K F (H x y))
    (hHsmulL : ∀ (a : F) x y, H (a • x) y = τ a * H x y)
    (hHsmulR : ∀ (a : F) x y, H x (a • y) = a * H x y)
    (hKF : ∀ (a : F) (x y : LinearMap.range e.mulVecLin),
        pslBTg4_h G ((a • x : LinearMap.range e.mulVecLin) : Fin n → K) (y : Fin n → K) =
        pslBTg4_h G (x : Fin n → K)
          ((τ a • y : LinearMap.range e.mulVecLin) : Fin n → K))
    (t : LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin)
    (htdet : LinearMap.det (t : LinearMap.range e.mulVecLin →ₗ[F] LinearMap.range e.mulVecLin) = 1)
    (htnot : ¬ (∀ x y, H (t x) (t y) = H x y)) : False := by
  haveI : Module.Finite K (LinearMap.range e.mulVecLin) := Module.Finite.of_finite
  haveI : Module.Finite F (LinearMap.range e.mulVecLin) :=
    Module.Finite.of_restrictScalars_finite K F (LinearMap.range e.mulVecLin)
  haveI : Module.Free F (LinearMap.range e.mulVecLin) :=
    Module.Free.of_divisionRing F (LinearMap.range e.mulVecLin)
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup
      (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F) := hperf
  let b : Module.Basis (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F
      (LinearMap.range e.mulVecLin) := Module.finBasis F (LinearMap.range e.mulVecLin)
  let bk : Matrix.SpecialLinearGroup (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F ≃*
      SpecialLinearGroup F (LinearMap.range e.mulVecLin) :=
    Matrix.SpecialLinearGroup.toLin_equiv b
  let iota : Matrix.SpecialLinearGroup (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →*
      (LinearMap.range e.mulVecLin ≃ₗ[F] LinearMap.range e.mulVecLin) :=
    SpecialLinearGroup.toLinearEquiv.comp bk.toMonoidHom
  let A : Matrix.SpecialLinearGroup (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →*
      GL (Fin n) K := ψ.comp iota
  have htriv : Matrix.GeneralLinearGroup.det.comp A = 1 :=
    pslBTg4_hom_trivial_of_perfect (Matrix.GeneralLinearGroup.det.comp A)
  have hdet : ∀ g, (A g : Matrix (Fin n) (Fin n) K).det = 1 := by
    intro g
    have h := congrArg (fun f : Matrix.SpecialLinearGroup
        (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →* Kˣ => f g) htriv
    simpa using congrArg Units.val h
  let slgHomFun : Matrix.SpecialLinearGroup
      (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →
      Matrix.SpecialLinearGroup (Fin n) K :=
    fun g => ⟨(A g : Matrix (Fin n) (Fin n) K), hdet g⟩
  let slgHom : Matrix.SpecialLinearGroup (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →*
      Matrix.SpecialLinearGroup (Fin n) K :=
    { toFun := slgHomFun
      map_one' := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_one]
        exact congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) (map_one A)
      map_mul' := fun g h => by
        apply Subtype.ext
        exact congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) (map_mul A g h) }
  have hmemP : ∀ g, slgHom g ∈ pslBlock B e := by
    intro g
    refine Subgroup.mem_comap.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · rw [Subgroup.mem_centralizer_iff]
      intro hB hBhB
      rw [Set.mem_singleton_iff] at hBhB
      subst hB
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact (hψB (iota g)).symm
    · exact hψfix (iota g)
  let φ : Matrix.SpecialLinearGroup (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F →*
      ↥(pslBlock B e) :=
    { toFun := fun g => ⟨slgHom g, hmemP g⟩
      map_one' := Subtype.ext (map_one slgHom)
      map_mul' := fun g h => Subtype.ext (map_mul slgHom g h) }
  let Y : Subgroup ↥(pslBlock B e) := MonoidHom.range φ
  have hY : Group.IsPerfect ↥Y := pslBTg4_range_perfect φ
  have hisog : ∀ g, formAdj (RingHom.id K) G
      ((ψ (iota g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((ψ (iota g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹ := by
    intro g
    have h := pslBT_isometry_of_perfect S Y hY ⟨φ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
    change formAdj (RingHom.id K) G
        ((ψ (iota g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((ψ (iota g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹ at h
    exact h
  have hmat : ∀ g, Matrix.transpose ((ψ (iota g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * G *
      ((ψ (iota g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = G := by
    intro g
    refine pslBTg4_transpose_mul_of_formAdj_inv S.det_isUnit (ψ (iota g)) ?_
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact hisog g
  have hpresg : ∀ g, ∀ x y : LinearMap.range e.mulVecLin,
      pslBTg4_h G ((iota g x : LinearMap.range e.mulVecLin) : Fin n → K)
        ((iota g y : LinearMap.range e.mulVecLin) : Fin n → K) =
      pslBTg4_h G (x : Fin n → K) (y : Fin n → K) := by
    intro g x y
    rw [← hψw (iota g) x, ← hψw (iota g) y]
    exact pslBTg4_h_preserved (hmat g) (x : Fin n → K) (y : Fin n → K)
  have hHpresg : ∀ g, ∀ x y : LinearMap.range e.mulVecLin, H (iota g x) (iota g y) = H x y := by
    intro g
    exact pslBTg4_H_preserved τ
      (fun x y : LinearMap.range e.mulVecLin => pslBTg4_h G (x : Fin n → K) (y : Fin n → K))
      H htrace hHsmulL hHsmulR hKF (iota g) (hpresg g)
  let sg : SpecialLinearGroup F (LinearMap.range e.mulVecLin) :=
    ⟨t, by apply Units.ext; simpa using htdet⟩
  let g0 : Matrix.SpecialLinearGroup (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F :=
    bk.symm sg
  have hiota : iota g0 = t := by
    have h1 : bk g0 = sg := bk.apply_symm_apply sg
    show (SpecialLinearGroup.toLinearEquiv) (bk g0) = t
    rw [h1]
    simpa using SpecialLinearGroup.toLinearEquiv_eq_coe sg
  exact htnot (fun x y => by
    have h := hHpresg g0 x y
    rwa [hiota] at h)

private lemma pslBTg4_dotProduct_smul {n : ℕ} {K : Type} [Field K] (c : K) (u w : Fin n → K) :
    u ⬝ᵥ (c • w) = c * (u ⬝ᵥ w) := by
  rw [dotProduct_comm u (c • w), smul_dotProduct, dotProduct_comm w u, smul_eq_mul]

private lemma pslBTg4_h_addL {n : ℕ} {K : Type} [Field K] (G : Matrix (Fin n) (Fin n) K)
    (x y z : Fin n → K) : pslBTg4_h G (x + y) z = pslBTg4_h G x z + pslBTg4_h G y z := by
  unfold pslBTg4_h
  rw [add_dotProduct]

private lemma pslBTg4_h_addR {n : ℕ} {K : Type} [Field K] (G : Matrix (Fin n) (Fin n) K)
    (x y z : Fin n → K) : pslBTg4_h G x (y + z) = pslBTg4_h G x y + pslBTg4_h G x z := by
  unfold pslBTg4_h
  rw [Matrix.mulVec_add, dotProduct_add]

private lemma pslBTg4_h_smulR {n : ℕ} {K : Type} [Field K] (G : Matrix (Fin n) (Fin n) K)
    (c : K) (x y : Fin n → K) : pslBTg4_h G x (c • y) = c * pslBTg4_h G x y := by
  unfold pslBTg4_h
  rw [Matrix.mulVec_smul, pslBTg4_dotProduct_smul]

private lemma pslBTg4_h_herm {n : ℕ} {K : Type} [Field K] {G : Matrix (Fin n) (Fin n) K}
    (hsymm : Gᵀ = G) (x y : Fin n → K) : pslBTg4_h G x y = pslBTg4_h G y x := by
  unfold pslBTg4_h
  conv_lhs => rw [← hsymm]
  rw [Matrix.dotProduct_transpose_mulVec]

private lemma pslBTg4_h_nd {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} (hG : IsUnit G.det)
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e) (hstar : formAdj (RingHom.id K) G e = e)
    (x : LinearMap.range e.mulVecLin)
    (hx : ∀ y : LinearMap.range e.mulVecLin,
      pslBTg4_h G (x : Fin n → K) (y : Fin n → K) = 0) : x = 0 := by
  have hGe : Matrix.transpose e * G = G * e := by
    have h := hstar
    rw [formAdj] at h
    have hmap : (e.map (RingHom.id K)) = e := by
      ext i j
      rfl
    rw [hmap] at h
    calc Matrix.transpose e * G
        = (G * G⁻¹) * (Matrix.transpose e * G) := by
          rw [Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
      _ = G * (G⁻¹ * Matrix.transpose e * G) := by simp only [Matrix.mul_assoc]
      _ = G * e := by rw [h]
  have hz : ∀ z : Fin n → K, pslBTg4_h G (x : Fin n → K) z = 0 := by
    intro z
    have h1 : pslBTg4_h G (x : Fin n → K) (e *ᵥ z) = 0 :=
      hx ⟨e *ᵥ z, LinearMap.mem_range.mpr ⟨z, Matrix.mulVecLin_apply e z⟩⟩
    have h2 : pslBTg4_h G (x : Fin n → K) ((1 - e) *ᵥ z) = 0 := by
      obtain ⟨v, hv⟩ := x.2
      have hv' : e *ᵥ v = (x : Fin n → K) := by simpa [Matrix.mulVecLin_apply] using hv
      have hxvec : (x : Fin n → K) = v ᵥ* Matrix.transpose e := by
        rw [← hv', Matrix.vecMul_transpose]
      calc pslBTg4_h G (x : Fin n → K) ((1 - e) *ᵥ z)
          = ((x : Fin n → K) ᵥ* (G * (1 - e))) ⬝ᵥ z := by
            unfold pslBTg4_h
            rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
        _ = 0 := by
            rw [hxvec, Matrix.vecMul_vecMul]
            have hz0 : Matrix.transpose e * (G * (1 - e)) = 0 := by
              rw [← Matrix.mul_assoc, hGe, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
                hee, sub_self, Matrix.mul_zero]
            rw [hz0, Matrix.vecMul_zero, zero_dotProduct]
    have hdecomp : z = e *ᵥ z + (1 - e) *ᵥ z := by
      rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
    calc pslBTg4_h G (x : Fin n → K) z
        = pslBTg4_h G (x : Fin n → K) (e *ᵥ z) +
            pslBTg4_h G (x : Fin n → K) ((1 - e) *ᵥ z) := by
          rw [← pslBTg4_h_addR, ← hdecomp]
      _ = 0 := by rw [h1, h2, add_zero]
  have hx0 : (x : Fin n → K) = 0 := by
    funext i
    have h := hz (G⁻¹ *ᵥ (Pi.single i 1))
    rw [pslBTg4_h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG, Matrix.one_mulVec] at h
    simp only [dotProduct] at h
    rw [Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  exact Subtype.ext hx0

private lemma pslBTg4_transpose_mul_eq_G_formAdj {n : ℕ} {K : Type} [Field K]
    {G : Matrix (Fin n) (Fin n) K} (hG : IsUnit G.det) (a : Matrix (Fin n) (Fin n) K) :
    Matrix.transpose a * G = G * formAdj (RingHom.id K) G a := by
  unfold formAdj
  have hmap : (a.map (RingHom.id K)) = a := by
    ext i j
    rfl
  rw [hmap]
  calc Matrix.transpose a * G
      = (G * G⁻¹) * (Matrix.transpose a * G) := by
        rw [Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
    _ = G * (G⁻¹ * Matrix.transpose a * G) := by simp only [Matrix.mul_assoc]

private lemma pslBTg4_h_adj {n : ℕ} {K : Type} [Field K] {G : Matrix (Fin n) (Fin n) K}
    (hG : IsUnit G.det) (a : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    pslBTg4_h G (a *ᵥ x) y = pslBTg4_h G x (formAdj (RingHom.id K) G a *ᵥ y) := by
  unfold pslBTg4_h
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose a x,
    Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec,
    pslBTg4_transpose_mul_eq_G_formAdj hG a]

private lemma pslBTg4_trace_form {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    {e : Matrix (Fin n) (Fin n) K} (hee : e * e = e)
    (hstar : formAdj (RingHom.id K) G e = e)
    {F : Type} [Field F] [Algebra K F] [Finite F]
    [Module F (LinearMap.range e.mulVecLin)]
    [IsScalarTower K F (LinearMap.range e.mulVecLin)]
    {π : pslAlg B →ₐ[K] F} (hπ : Function.Surjective π)
    (hact : ∀ (a : pslAlg B) (w : LinearMap.range e.mulVecLin),
      ((π a • w : LinearMap.range e.mulVecLin) : Fin n → K) =
        (a : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K))
    (τ : F ≃+* F) (hττ : ∀ x, τ (τ x) = x)
    (hτσ : ∀ c : K, τ (algebraMap K F c) = algebraMap K F c)
    (hτπ : ∀ a : pslAlg B, τ (π a) =
      π ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
        pslGraph_star_mem S (a : Matrix (Fin n) (Fin n) K) a.2⟩) :
    ∃ H : LinearMap.range e.mulVecLin → LinearMap.range e.mulVecLin → F,
      (∀ x y z, H (x + y) z = H x z + H y z) ∧
      (∀ x y z, H x (y + z) = H x y + H x z) ∧
      (∀ (a : F) x y, H (a • x) y = τ a * H x y) ∧
      (∀ (a : F) x y, H x (a • y) = a * H x y) ∧
      (∀ x y, H x y = τ (H y x)) ∧
      (∀ x, (∀ y, H x y = 0) → x = 0) ∧
      (∀ (x y : LinearMap.range e.mulVecLin),
        pslBTg4_h G (x : Fin n → K) (y : Fin n → K) = Algebra.trace K F (H x y)) := by
  have hKF : ∀ (a : F) (x y : LinearMap.range e.mulVecLin),
      pslBTg4_h G (((a • x : LinearMap.range e.mulVecLin)) : Fin n → K) (y : Fin n → K) =
      pslBTg4_h G (x : Fin n → K)
        (((τ a • y : LinearMap.range e.mulVecLin)) : Fin n → K) := by
    intro a x y
    obtain ⟨a0, rfl⟩ := hπ a
    have hx : ((π a0 • x : LinearMap.range e.mulVecLin) : Fin n → K) =
        (a0 : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → K) := hact a0 x
    have hy : ((τ (π a0) • y : LinearMap.range e.mulVecLin) : Fin n → K) =
        (formAdj (RingHom.id K) G (a0 : Matrix (Fin n) (Fin n) K)) *ᵥ (y : Fin n → K) := by
      rw [hτπ a0]
      exact hact ⟨formAdj (RingHom.id K) G (a0 : Matrix (Fin n) (Fin n) K),
        pslGraph_star_mem S (a0 : Matrix (Fin n) (Fin n) K) a0.2⟩ y
    rw [hx, hy]
    exact pslBTg4_h_adj S.det_isUnit (a0 : Matrix (Fin n) (Fin n) K) (x : Fin n → K)
      (y : Fin n → K)
  exact pslBT_traceTransfer (σ := RingHom.id K) (τ := τ) (hσσ := fun c => rfl) (hττ := hττ)
    (hτσ := hτσ)
    (hK := fun (x y : LinearMap.range e.mulVecLin) => pslBTg4_h G (x : Fin n → K) (y : Fin n → K))
    (hKaddL := fun x y z => pslBTg4_h_addL G _ _ _)
    (hKaddR := fun x y z => pslBTg4_h_addR G _ _ _)
    (hKsmulR := fun c x y => pslBTg4_h_smulR G c _ _)
    (hKherm := fun x y => pslBTg4_h_herm S.symm _ _)
    (hKnd := fun x hx => pslBTg4_h_nd S.det_isUnit hee hstar _ hx)
    (hKF := hKF)

private lemma pslBTg4_pslAlg_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a ∈ pslAlg B, ∀ b ∈ pslAlg B, a * b = b * a := by
  have hcommS : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  letI : CommSemiring (pslAlg B) := Algebra.adjoinCommSemiringOfComm K hcommS
  intro a ha b hb
  have h := mul_comm (⟨a, ha⟩ : pslAlg B) (⟨b, hb⟩ : pslAlg B)
  simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h

private lemma pslBTg4_sl_perfect {F F' : Type} [Field F] [Finite F] [CharP F 2]
    (k : ℕ) (hk2 : 2 ≤ k)
    (hnot : ¬ (k = 2 ∧ Nat.card F' = 2)) (hcard : Nat.card F = Nat.card F') :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin k) F) := by
  haveI : Fintype F := Fintype.ofFinite F
  refine CFSG.LinearGroups.special_linear_isPerfect hk2 ?_
  by_cases hk3 : 3 ≤ k
  · exact Or.inl hk3
  · right
    have hk2' : k = 2 := by omega
    have hFne2 : Nat.card F ≠ 2 := by
      intro h
      exact hnot ⟨hk2', by rw [← hcard]; exact h⟩
    have hFne3 : Nat.card F ≠ 3 := by
      intro h3
      have h0 : (Nat.card F : F) = 0 := by
        rw [Nat.card_eq_fintype_card]
        exact Nat.cast_card_eq_zero F
      rw [h3] at h0
      have hdiv : 2 ∣ 3 := (CharP.cast_eq_zero_iff F 2 3).mp h0
      norm_num at hdiv
    have hF2 : 2 ≤ Nat.card F := by
      have h := Fintype.one_lt_card (α := F)
      rw [Nat.card_eq_fintype_card]
      omega
    have hcard_ge : 4 ≤ Nat.card F := by omega
    have h4 : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact hcard_ge
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := Finset.univ) h4
    exact ⟨s, hs⟩

private lemma pslBTg4_tauI_pi {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    {e : Matrix (Fin n) (Fin n) K} (heB : e ∈ pslAlg B) (hstar : formAdj (RingHom.id K) G e = e)
    {F : Type} [Field F] [Algebra K F]
    {π : pslAlg B →ₐ[K] F} (hker : ∀ a : pslAlg B, π a = 0 ↔ (a : Matrix (Fin n) (Fin n) K) * e = 0)
    (hI2 : ∀ a ∈ pslAlg B,
      formAdj (RingHom.id K) G (a * e) = a * e) :
    ∀ a : pslAlg B, π a =
      π ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
        pslGraph_star_mem S (a : Matrix (Fin n) (Fin n) K) a.2⟩ := by
  intro a
  have hstara : formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K) ∈ pslAlg B :=
    pslGraph_star_mem S (a : Matrix (Fin n) (Fin n) K) a.2
  have hcomm : e * formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K) =
      formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K) * e :=
    pslBTg4_pslAlg_comm B e heB _ hstara
  have hfa : formAdj (RingHom.id K) G ((a : Matrix (Fin n) (Fin n) K) * e) =
      formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K) * e := by
    rw [Geo.formAdj_mul (RingHom.id K) S.det_isUnit (a : Matrix (Fin n) (Fin n) K) e, hstar, hcomm]
  have hae : formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K) * e =
      (a : Matrix (Fin n) (Fin n) K) * e := by
    rw [← hfa]
    exact hI2 (a : Matrix (Fin n) (Fin n) K) a.2
  have hdiff : (formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K) -
      (a : Matrix (Fin n) (Fin n) K)) * e = 0 := by
    rw [Matrix.sub_mul, hae, sub_self]
  have hpi : π ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
      pslGraph_star_mem S (a : Matrix (Fin n) (Fin n) K) a.2⟩ = π a := by
    have h0 : π (⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
        pslGraph_star_mem S (a : Matrix (Fin n) (Fin n) K) a.2⟩ - a) = 0 := by
      apply (hker _).mpr
      simpa using hdiff
    rwa [map_sub, sub_eq_zero] at h0
  exact hpi.symm

private lemma pslBT_II_perfect_eq_bot {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hII : pslTypeII G B e)
    (Y : Subgroup ↥(pslBlock B e)) (hY : Group.IsPerfect ↥Y) : Y = ⊥ := by
  by_contra hYne
  haveI : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hYne
  haveI : Group.IsPerfect ↥Y := hY
  have hns : ¬ Group.IsSolvable ↥(pslBlock B e) := by
    intro hsol
    letI : Group.IsSolvable ↥(pslBlock B e) := hsol
    exact Group.IsPerfect.not_isSolvable ↥Y
      (solvable_of_solvable_injective (f := Subgroup.subtype Y) Subtype.coe_injective)
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, hact, hrank,
    hpos, hψinj, hψw, hψfix, hψe, hψB⟩ :=
    exists_blockEmbed S.odd rfl ((hP.1 e).mp he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Module F (LinearMap.range e.mulVecLin) := hM
  letI : IsScalarTower K F (LinearMap.range e.mulVecLin) := hT
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Module.Finite K F := Module.Finite.of_finite
  haveI : Algebra.IsSeparable K F := by infer_instance
  have hee : e * e = e := IsIdempotentElem.eq ((hP.1 e).mp he).2.1
  have hstar : formAdj (RingHom.id K) G e = e := hII.1
  obtain ⟨τ, hττ, hτK, hτπ⟩ :=
    pslBT_tau S ((hP.1 e).mp he).1 hstar π hπ hker
  obtain ⟨F', hFld', hFin', hChar', k, hcard', hrank', hk2, hnot, φ', hφ'inj⟩ :=
    pslBT_nonsolvable_params S P hP e he hns
  have hdpos : 0 < blockDegree (pslAlg B) e := by
    by_contra hd
    have hd0 : blockDegree (pslAlg B) e = 0 := Nat.eq_zero_of_not_pos hd
    rw [hd0, pow_zero] at hcard
    have h2 : 2 ≤ Nat.card F := by
      have h := Fintype.one_lt_card (α := F)
      rw [Nat.card_eq_fintype_card]
      omega
    omega
  have hkfin : Module.finrank F (LinearMap.range e.mulVecLin) = k := by
    have h : blockDegree (pslAlg B) e * Module.finrank F (LinearMap.range e.mulVecLin) =
        blockDegree (pslAlg B) e * k := by
      calc blockDegree (pslAlg B) e * Module.finrank F (LinearMap.range e.mulVecLin)
          = Module.finrank K F * Module.finrank F (LinearMap.range e.mulVecLin) := by
            rw [hdim]
        _ = Matrix.rank e := hrank.symm
        _ = blockDegree (pslAlg B) e * k := hrank'
    exact Nat.mul_left_cancel hdpos h
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup
      (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F) := by
    rw [hkfin]
    exact pslBTg4_sl_perfect k hk2 hnot (by rw [hcard, hcard'])
  have hneτ : ∃ x, τ x ≠ x := by
    obtain ⟨a, ha, hne⟩ := hII.2
    refine ⟨π ⟨a, ha⟩, fun hfix => ?_⟩
    have hτa : τ (π ⟨a, ha⟩) = π ⟨formAdj (RingHom.id K) G a, pslGraph_star_mem S a ha⟩ :=
      hτπ ⟨a, ha⟩
    have hπeq : π ⟨formAdj (RingHom.id K) G a, pslGraph_star_mem S a ha⟩ = π ⟨a, ha⟩ := by
      rw [← hτa]
      exact hfix
    have hker0 : (formAdj (RingHom.id K) G a - a) * e = 0 := by
      have hpi : π (⟨formAdj (RingHom.id K) G a, pslGraph_star_mem S a ha⟩ - ⟨a, ha⟩ :
          pslAlg B) = 0 := by
        rw [map_sub, hπeq, sub_self]
      have h := (hker (⟨formAdj (RingHom.id K) G a, pslGraph_star_mem S a ha⟩ -
        ⟨a, ha⟩)).mp hpi
      simpa using h
    have hae : formAdj (RingHom.id K) G a * e = a * e := by
      have h := hker0
      rwa [Matrix.sub_mul, sub_eq_zero] at h
    have hcommstar : e * formAdj (RingHom.id K) G a = formAdj (RingHom.id K) G a * e :=
      pslBTg4_pslAlg_comm B e ((hP.1 e).mp he).1 (formAdj (RingHom.id K) G a)
        (pslGraph_star_mem S a ha)
    have hform : formAdj (RingHom.id K) G (a * e) = formAdj (RingHom.id K) G a * e := by
      rw [Geo.formAdj_mul (RingHom.id K) S.det_isUnit a e, hstar, hcommstar]
    exact hne (by rw [hform, hae])
  have hτU : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution τ :=
    pslBT_isUnitaryInvolution τ hττ hneτ
  have hKF : ∀ (a : F) (x y : LinearMap.range e.mulVecLin),
      pslBTg4_h G (((a • x : LinearMap.range e.mulVecLin)) : Fin n → K) (y : Fin n → K) =
      pslBTg4_h G (x : Fin n → K)
        (((τ a • y : LinearMap.range e.mulVecLin)) : Fin n → K) := by
    intro a x y
    obtain ⟨a0, rfl⟩ := hπ a
    have hx : ((π a0 • x : LinearMap.range e.mulVecLin) : Fin n → K) =
        (a0 : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → K) := hact a0 x
    have hy : ((τ (π a0) • y : LinearMap.range e.mulVecLin) : Fin n → K) =
        (formAdj (RingHom.id K) G (a0 : Matrix (Fin n) (Fin n) K)) *ᵥ (y : Fin n → K) := by
      rw [hτπ a0]
      exact hact ⟨formAdj (RingHom.id K) G (a0 : Matrix (Fin n) (Fin n) K),
        pslGraph_star_mem S (a0 : Matrix (Fin n) (Fin n) K) a0.2⟩ y
    rw [hx, hy]
    exact pslBTg4_h_adj S.det_isUnit (a0 : Matrix (Fin n) (Fin n) K) (x : Fin n → K)
      (y : Fin n → K)
  obtain ⟨H, hHaddL, hHaddR, hHsmulL, hHsmulR, hHherm, hHnd, hHtrace⟩ :=
    pslBTg4_trace_form S hee hstar hπ hact τ hττ (fun c => hτK c) hτπ
  haveI : Module.Finite F (LinearMap.range e.mulVecLin) :=
    Module.Finite.of_restrictScalars_finite K F (LinearMap.range e.mulVecLin)
  haveI : Nontrivial (LinearMap.range e.mulVecLin) :=
    Module.nontrivial_of_finrank_pos (R := F) (by rw [hkfin]; omega)
  obtain ⟨v0, hv0⟩ := exists_anisotropic_of_hermitian τ hτU.exists_ne H hHherm hHaddL hHsmulL
    hHaddR hHsmulR hHnd
  obtain ⟨t, htdet, htnot⟩ := exists_transvection_not_isometry H (by rw [hkfin]; exact hk2)
    hHaddR hHsmulR ⟨v0, hv0⟩
  exact pslBTg4_copy_contra S ψ hψw hψfix hψB hperf τ H hHtrace hHsmulL hHsmulR hKF
    t htdet htnot

private lemma pslBT_I_rank {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hI : pslTypeI G B e)
    (hns : ¬ Group.IsSolvable ↥(pslBlock B e)) :
    Matrix.rank e = 2 * blockDegree (pslAlg B) e := by
  obtain ⟨F, hFld, hAlg, hFin, hChar, π, hM, hT, ψ, hπ, hker, hdim, hcard, hact, hrank,
    hpos, hψinj, hψw, hψfix, hψe, hψB⟩ :=
    exists_blockEmbed S.odd rfl ((hP.1 e).mp he)
  letI : Field F := hFld
  letI : Algebra K F := hAlg
  letI : Module F (LinearMap.range e.mulVecLin) := hM
  letI : IsScalarTower K F (LinearMap.range e.mulVecLin) := hT
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Module.Finite K F := Module.Finite.of_finite
  haveI : Algebra.IsSeparable K F := by infer_instance
  have hee : e * e = e := IsIdempotentElem.eq ((hP.1 e).mp he).2.1
  have hstar : formAdj (RingHom.id K) G e = e := hI.1
  obtain ⟨F', hFld', hFin', hChar', k, hcard', hrank', hk2, hnot, φ', hφ'inj⟩ :=
    pslBT_nonsolvable_params S P hP e he hns
  have hdpos : 0 < blockDegree (pslAlg B) e := by
    by_contra hd
    have hd0 : blockDegree (pslAlg B) e = 0 := Nat.eq_zero_of_not_pos hd
    rw [hd0, pow_zero] at hcard
    have h2 : 2 ≤ Nat.card F := by
      have h := Fintype.one_lt_card (α := F)
      rw [Nat.card_eq_fintype_card]
      omega
    omega
  have hkfin : Module.finrank F (LinearMap.range e.mulVecLin) = k := by
    have h : blockDegree (pslAlg B) e * Module.finrank F (LinearMap.range e.mulVecLin) =
        blockDegree (pslAlg B) e * k := by
      calc blockDegree (pslAlg B) e * Module.finrank F (LinearMap.range e.mulVecLin)
          = Module.finrank K F * Module.finrank F (LinearMap.range e.mulVecLin) := by
            rw [hdim]
        _ = Matrix.rank e := hrank.symm
        _ = blockDegree (pslAlg B) e * k := hrank'
    exact Nat.mul_left_cancel hdpos h
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup
      (Fin (Module.finrank F (LinearMap.range e.mulVecLin))) F) := by
    rw [hkfin]
    exact pslBTg4_sl_perfect k hk2 hnot (by rw [hcard, hcard'])
  have hτπI : ∀ a : pslAlg B, π a =
      π ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
        pslGraph_star_mem S (a : Matrix (Fin n) (Fin n) K) a.2⟩ :=
    pslBTg4_tauI_pi S ((hP.1 e).mp he).1 hstar hker hI.2
  have hτπIr : ∀ a : pslAlg B, (RingEquiv.refl F) (π a) =
      π ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
        pslGraph_star_mem S (a : Matrix (Fin n) (Fin n) K) a.2⟩ :=
    fun a => hτπI a
  have hKF : ∀ (a : F) (x y : LinearMap.range e.mulVecLin),
      pslBTg4_h G (((a • x : LinearMap.range e.mulVecLin)) : Fin n → K) (y : Fin n → K) =
      pslBTg4_h G (x : Fin n → K)
        ((((RingEquiv.refl F) a • y : LinearMap.range e.mulVecLin)) : Fin n → K) := by
    intro a x y
    obtain ⟨a0, rfl⟩ := hπ a
    have hx : ((π a0 • x : LinearMap.range e.mulVecLin) : Fin n → K) =
        (a0 : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → K) := hact a0 x
    have hy : (((RingEquiv.refl F) (π a0) • y : LinearMap.range e.mulVecLin) : Fin n → K) =
        (formAdj (RingHom.id K) G (a0 : Matrix (Fin n) (Fin n) K)) *ᵥ (y : Fin n → K) := by
      change ((π a0 • y : LinearMap.range e.mulVecLin) : Fin n → K) =
        (formAdj (RingHom.id K) G (a0 : Matrix (Fin n) (Fin n) K)) *ᵥ (y : Fin n → K)
      rw [hτπI a0]
      exact hact ⟨formAdj (RingHom.id K) G (a0 : Matrix (Fin n) (Fin n) K),
        pslGraph_star_mem S (a0 : Matrix (Fin n) (Fin n) K) a0.2⟩ y
    rw [hx, hy]
    exact pslBTg4_h_adj S.det_isUnit (a0 : Matrix (Fin n) (Fin n) K) (x : Fin n → K)
      (y : Fin n → K)
  obtain ⟨H, hHaddL, hHaddR, hHsmulL, hHsmulR, hHherm, hHnd, hHtrace⟩ :=
    pslBTg4_trace_form S hee hstar hπ hact (RingEquiv.refl F)
      (fun x => rfl) (fun c => rfl) hτπIr
  haveI : Module.Finite F (LinearMap.range e.mulVecLin) :=
    Module.Finite.of_restrictScalars_finite K F (LinearMap.range e.mulVecLin)
  have hk2fin : 2 ≤ Module.finrank F (LinearMap.range e.mulVecLin) := by
    rw [hkfin]
    exact hk2
  have hle2 : Module.finrank F (LinearMap.range e.mulVecLin) ≤ 2 := by
    by_contra hge
    have h3 : 3 ≤ Module.finrank F (LinearMap.range e.mulVecLin) := by omega
    by_cases haniso : ∃ v, H v v ≠ 0
    · obtain ⟨v0, hv0⟩ := haniso
      obtain ⟨t, htdet, htnot⟩ := exists_transvection_not_isometry H hk2fin hHaddR hHsmulR
        ⟨v0, hv0⟩
      exact pslBTg4_copy_contra S ψ hψw hψfix hψB hperf (RingEquiv.refl F) H hHtrace
        hHsmulL hHsmulR hKF t htdet htnot
    · have halt : ∀ v, H v v = 0 := fun v => not_not.mp (fun hv => haniso ⟨v, hv⟩)
      obtain ⟨t, htdet, htnot⟩ := exists_transvection_not_isometry_of_alternating H h3 hHaddL
        hHaddR hHsmulR halt hHnd
      exact pslBTg4_copy_contra S ψ hψw hψfix hψB hperf (RingEquiv.refl F) H hHtrace
        hHsmulL hHsmulR hKF t htdet htnot
  have hk_eq : Module.finrank F (LinearMap.range e.mulVecLin) = 2 := by omega
  calc Matrix.rank e = Module.finrank K F * Module.finrank F (LinearMap.range e.mulVecLin) := hrank
    _ = blockDegree (pslAlg B) e * 2 := by rw [hdim, hk_eq]
    _ = 2 * blockDegree (pslAlg B) e := by ring

private lemma pslBT_I_card {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hI : pslTypeI G B e)
    (hns : ¬ Group.IsSolvable ↥(pslBlock B e)) :
    4 ≤ Nat.card K ^ blockDegree (pslAlg B) e := by
  obtain ⟨F, hFld, hFin, hChar, k, hcard, hrank, hk2, hnot, φ, hφinj⟩ :=
    pslBT_nonsolvable_params S P hP e he hns
  letI : Field F := hFld
  letI : Finite F := hFin
  letI : CharP F 2 := hChar
  haveI : Fintype F := Fintype.ofFinite F
  have hrankI := pslBT_I_rank S P hP e he hI hns
  have hF2 : 2 ≤ Nat.card F := by
    have h := Fintype.one_lt_card (α := F)
    rw [Nat.card_eq_fintype_card]
    omega
  have hdpos : 0 < blockDegree (pslAlg B) e := by
    by_contra hd
    have hd0 : blockDegree (pslAlg B) e = 0 := Nat.eq_zero_of_not_pos hd
    rw [hd0, pow_zero] at hcard
    omega
  have hk_eq : k = 2 := by
    have h : blockDegree (pslAlg B) e * k = blockDegree (pslAlg B) e * 2 := by
      rw [← hrank, hrankI]
      ring
    exact Nat.mul_left_cancel hdpos h
  have hFne2 : Nat.card F ≠ 2 := fun h => hnot ⟨hk_eq, h⟩
  have hFne3 : Nat.card F ≠ 3 := by
    intro h3
    have h0 : (Nat.card F : F) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.cast_card_eq_zero F
    rw [h3] at h0
    have hdiv : 2 ∣ 3 := (CharP.cast_eq_zero_iff F 2 3).mp h0
    norm_num at hdiv
  have h4 : 4 ≤ Nat.card F := by omega
  rwa [hcard] at h4

theorem pslGraph_typeIII_solvable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hne : formAdj (RingHom.id K) G e ≠ e) :
    Group.IsSolvable ↥(pslBlock B e) := by
  exact pslBT_solvable_of_forall_perfect_eq_bot (G := ↥(pslBlock B e))
    (fun Y hY => pslBT_III_perfect_eq_bot S P hP e he hne Y hY)

theorem pslGraph_typeII_solvable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hII : pslTypeII G B e) :
    Group.IsSolvable ↥(pslBlock B e) := by
  exact pslBT_solvable_of_forall_perfect_eq_bot (G := ↥(pslBlock B e))
    (fun Y hY => pslBT_II_perfect_eq_bot S P hP e he hII Y hY)

theorem pslGraph_typeI_two {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ P) (hI : pslTypeI G B e)
    (hns : ¬ Group.IsSolvable ↥(pslBlock B e)) :
    Matrix.rank e = 2 * blockDegree (pslAlg B) e ∧
      4 ≤ Nat.card K ^ blockDegree (pslAlg B) e := by
  exact ⟨pslBT_I_rank S P hP e he hI hns, pslBT_I_card S P hP e he hI hns⟩

end CFSG.StandardType
