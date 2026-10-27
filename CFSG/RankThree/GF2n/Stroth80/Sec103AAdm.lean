module

public import CFSG.RankThree.GF2n.Stroth80.Sec103ABad

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

variable {hc : Ctx M Q Z B} {n : ℕ} {t : G} {Y : Subgroup G}

structure Adm103 (M Q Z B : Subgroup G) (t : G) (Y : Subgroup G) (c : G) : Prop where
  mem : c ∈ Q
  centB : c ∈ Subgroup.centralizer (B : Set G)
  notW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)
  exα : ∃ α ∈ Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G), α ∉ Vt M (LB M Q B) B Z t
  card : Nat.card Z * Nat.card ↥(Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ⊓
      Subgroup.centralizer ({c} : Set G)) ≤
    Nat.card ↥(Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G))


private lemma image_imgSub_Vt_card_eq_pow
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) {m : ℕ} (hsl : SLMNat hc t m) :
    Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c e he => hc.smul_mem_img_Vt hD t c he)) = Nat.card K ^ m := by
  have hVcard := hsl.card_Vt
  have hVdec := M₀.card_eq (hc.Vt_le_Q t)
    (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z) (t := t))
  have hKpos : 0 < Nat.card K := by
    have hq := hc.hyp.q4
    rw [← hD.card] at hq
    omega
  have hWimg : Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c e he => hc.smul_mem_img_Vt hD t c he)) =
      Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) := rfl
  have hkey : Nat.card K * Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c e he => hc.smul_mem_img_Vt hD t c he)) =
      Nat.card K * Nat.card K ^ m := by
    calc Nat.card K * Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t)
          (fun c e he => hc.smul_mem_img_Vt hD t c he))
        = Nat.card K * Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) := by rw [hWimg]
      _ = Nat.card Z * Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) := by rw [hD.card]
      _ = Nat.card (Vt M (LB M Q B) B Z t) := hVdec.symm
      _ = Nat.card Z ^ (m + 1) := hVcard
      _ = Nat.card Z * Nat.card Z ^ m := by rw [pow_succ]; ring
      _ = Nat.card K * Nat.card K ^ m := by rw [← hD.card]
  exact Nat.mul_left_cancel hKpos hkey

private lemma orthogonal_le_image_Vt_of_mem
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) {α : G} (hα : α ∈ Q) {b : M₀.E}
    (hb : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    {P : Submodule K M₀.E} (hαP : M₀.π α ∈ P) (hbP : b ∈ P)
    (hno : ∀ c ∈ Q, c * α = α * c → c ∈ Subgroup.centralizer (B : Set G) →
      c ∈ Wt Q (Vt M (LB M Q B) B Z t)) :
    M₀.B.orthogonal P ≤ M₀.B.orthogonal (imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c e he => hc.smul_mem_img_Vt hD t c he)) := by
  intro e he
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at he ⊢
  intro v hv
  obtain ⟨c, hcQ, hπ⟩ := M₀.π_surj e
  have hcα : c * α = α * c := by
    rw [Tim79.QuadModel.comm_iff_B M₀ hD.reg hcQ hα]
    rw [hπ, Tim79.QuadModel.B_comm, he (M₀.π α) hαP, neg_zero]
  have hcB : c ∈ Subgroup.centralizer (B : Set G) := by
    rw [Tim79.QuadModel.centralizer_iff hD.reg hc.le hb hcQ]
    rw [hπ, Tim79.QuadModel.B_comm, he b hbP, neg_zero]
  have hBorth : ∀ u ∈ M₀.img (Vt M (LB M Q B) B Z t), M₀.B (M₀.π c) u = 0 :=
    (mem_img_Wt_iff M₀ hD.reg (hc.Vt_le_Q t)).mp
      (M₀.pi_mem_img (hno c hcQ hcα hcB) hcQ)
  rw [← hπ, Tim79.QuadModel.B_comm, hBorth v (mem_imgSub.mp hv), neg_zero]

private lemma pi_mem_image_Vt_of_le_span
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) {m : ℕ} (hm : 2 ≤ m) {α : G} {b : M₀.E}
    (hWcard : Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c e he => hc.smul_mem_img_Vt hD t c he)) = Nat.card K ^ m)
    (hWP : imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c e he => hc.smul_mem_img_Vt hD t c he) ≤
        Submodule.span K ({M₀.π α, b} : Set M₀.E))
    (hPdim : Module.finrank K ↥(Submodule.span K ({M₀.π α, b} : Set M₀.E)) ≤ 2) :
    M₀.π α ∈ imgSub M₀ (Vt M (LB M Q B) B Z t)
      (fun c e he => hc.smul_mem_img_Vt hD t c he) := by
  classical
  haveI : Finite M₀.E := Module.finite_of_finite K
  let W : Submodule K M₀.E := imgSub M₀ (Vt M (LB M Q B) B Z t)
    (fun c e he => hc.smul_mem_img_Vt hD t c he)
  let P : Submodule K M₀.E := Submodule.span K ({M₀.π α, b} : Set M₀.E)
  have hWleP : Nat.card ↥W ≤ Nat.card ↥P :=
    Nat.card_le_card_of_injective (fun x : W => (⟨x.1, hWP x.2⟩ : P))
      fun x y hxy => Subtype.ext (congrArg (fun z : P => (z : M₀.E)) hxy)
  have hK2 : 2 ≤ Nat.card K := by
    have := hc.hyp.q4; rw [← hD.card] at this; omega
  have hmle : m ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card K)).mp
    calc Nat.card K ^ m = Nat.card ↥W := hWcard.symm
      _ ≤ Nat.card ↥P := hWleP
      _ ≤ Nat.card K ^ 2 := by
        rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥P)]
        exact Nat.pow_le_pow_right (by omega : 0 < Nat.card K) hPdim
  have hm2 : m = 2 := le_antisymm hmle hm
  have hWfin : Module.finrank K ↥W = m := by
    apply Nat.pow_right_injective hK2
    change Nat.card K ^ Module.finrank K ↥W = Nat.card K ^ m
    rw [← Module.natCard_eq_pow_finrank (K := K) (V := ↥W), hWcard]
  have hPfin : Module.finrank K ↥P = 2 := by
    refine le_antisymm hPdim ?_
    apply (Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card K)).mp
    calc Nat.card K ^ 2 = Nat.card K ^ m := by rw [hm2]
      _ = Nat.card ↥W := hWcard.symm
      _ ≤ Nat.card ↥P := hWleP
      _ = Nat.card K ^ Module.finrank K ↥P := Module.natCard_eq_pow_finrank
  have hWeq : W = P := Submodule.eq_of_le_of_finrank_eq hWP (by rw [hWfin, hm2, hPfin])
  change M₀.π α ∈ W
  rw [hWeq]
  exact Submodule.subset_span (by simp)


theorem SLMNat.exists_mem_centralizer_not_mem_Wt_of_not_mem_Vt {hc : Ctx M Q Z B} {t : G}
    {m : ℕ} (hm : SLMNat hc t m) (hm2 : 2 ≤ m) {α : G} (hα : α ∈ Q)
    (hαV : α ∉ Vt M (LB M Q B) B Z t) :
    ∃ c ∈ Q, c * α = α * c ∧ c ∈ Subgroup.centralizer (B : Set G) ∧
      c ∉ Wt Q (Vt M (LB M Q B) B Z t) := by
  classical
  by_contra hcon
  obtain ⟨K, fK, finK, chK, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  haveI : Finite M₀.E := Module.finite_of_finite K
  obtain ⟨g, hg⟩ := hc.conj
  have hBline : M₀.IsLine B := by
    rw [hg]
    exact hD.line g (by rw [← hg]; exact hc.ne) (by rw [← hg]; exact hc.le)
  obtain ⟨b, hb0, hb⟩ := hBline
  let V : Subgroup G := Vt M (LB M Q B) B Z t
  let W : Submodule K M₀.E := imgSub M₀ V (fun c e he => hc.smul_mem_img_Vt hD t c he)
  let P : Submodule K M₀.E := Submodule.span K ({M₀.π α, b} : Set M₀.E)
  have hPdim : Module.finrank K ↥P ≤ 2 := by
    have hspan : (({M₀.π α, b} : Finset M₀.E) : Set M₀.E) =
        ({M₀.π α, b} : Set M₀.E) := by ext x; simp
    have h := finrank_span_finset_le_card (R := K) (s := ({M₀.π α, b} : Finset M₀.E))
    rw [hspan] at h
    have h2 : ({M₀.π α, b} : Finset M₀.E).card ≤ 2 := Finset.card_le_two
    simpa [P, Set.finrank] using h.trans h2
  have hZV : Z ≤ V := sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z) (t := t)
  have hno : ∀ c ∈ Q, c * α = α * c → c ∈ Subgroup.centralizer (B : Set G) →
      c ∈ Wt Q V := by
    intro c hcQ hcα hcB
    by_contra hcW
    exact hcon ⟨c, hcQ, hcα, hcB, hcW⟩
  have hαP : M₀.π α ∈ P := Submodule.subset_span (by simp)
  have hbP : b ∈ P := Submodule.subset_span (by simp)
  have horth := orthogonal_le_image_Vt_of_mem (hc := hc) hD hα hb hαP hbP hno
  have hWP : W ≤ P := by
    have hnd : M₀.B.Nondegenerate := modelB_nondegenerate M₀
    have hrefl : M₀.B.IsRefl := fun x y hxy => by
      rw [Tim79.QuadModel.B_comm, hxy, neg_zero]
    have h1 := LinearMap.BilinForm.orthogonal_le (B := M₀.B) horth
    rwa [LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl,
      LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl] at h1
  have hWcard := image_imgSub_Vt_card_eq_pow (hc := hc) hD hm
  have hπα := pi_mem_image_Vt_of_le_span (hc := hc) hD hm2 hWcard hWP hPdim
  exact hαV ((M₀.mem_img_iff hZV hα).mp (mem_imgSub.mp hπα))

theorem Good101.exists_mem_centralizer_not_mem_Wt {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {α : G} (hαQ : α ∈ Q)
    (hαV : α ∉ Vt M (LB M Q B) B Z t) :
    ∃ c ∈ Q, c * α = α * c ∧ c ∈ Subgroup.centralizer (B : Set G) ∧
      c ∉ Wt Q (Vt M (LB M Q B) B Z t) := by
  obtain ⟨m, hm2, hm⟩ := SLlike.exists_SLMNat (H.slLike ht)
  exact SLMNat.exists_mem_centralizer_not_mem_Wt_of_not_mem_Vt hm hm2 hαQ hαV

theorem BadA.exists_root_group_of_not_mem_Wt (D : BadA hc n t Y) {c : G} (hcQ : c ∈ Q)
    (hcW : c ∉ Wt Q (Vt M (LB M Q B) B Z t)) :
    ∃ X : Subgroup G, Ctx M Q Z X ∧ X ≤ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ∧ Y ≤ QB X ∧
      ¬ X ≤ Subgroup.centralizer ({c} : Set G) := by
  have hv : ∃ v ∈ Vt M (LB M Q B) B Z t, v * c ≠ c * v := by
    by_contra hcon
    push Not at hcon
    exact hcW ⟨hcQ, Subgroup.mem_centralizer_iff.mpr fun v hv => hcon v hv⟩
  obtain ⟨v, hvV, hvc⟩ := hv
  have hAN : Q ⊓ QB Y ≤ Subgroup.normalizer (Z : Set G) :=
    fun _ ha => hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 ha.1)
  obtain ⟨a, haA, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hAN (D.Vt_le hvV)
  have haV : a ∈ Vt M (LB M Q B) B Z t := by
    have e : a = a * z * z⁻¹ := by group
    rw [e]
    exact (Vt _ _ _ _ _).mul_mem hvV ((Vt _ _ _ _ _).inv_mem (sec39_Z_le_Vt hz))
  have hzc : z * c = c * z := Z_central hc.hyp hz hcQ
  have hac : a * c ≠ c * a := fun h => hvc (by
    calc a * z * c = a * (z * c) := by group
      _ = a * (c * z) := by rw [hzc]
      _ = (a * c) * z := by group
      _ = (c * a) * z := by rw [h]
      _ = c * (a * z) := by group)
  have ha1 : a ≠ 1 := fun h => hac (by rw [h, one_mul, mul_one])
  have hZY : Z ⊓ QB Y = ⊥ := Z_inf_QB_eq_bot D.hs (smith_1_12 D.hs)
  have haZ : a ∉ Z := fun h => ha1 (by
    have h' : a ∈ Z ⊓ QB Y := ⟨h, haA.2⟩
    rwa [hZY, Subgroup.mem_bot] at h')
  obtain ⟨C, hC, haC, hCY, hYC⟩ :=
    Sit.exists_root_group D.hs haA ha1 (Good101.isRoot_of_mem_Vt D.H D.ht haV haZ)
  refine ⟨C, hC, fun e he => ?_, hYC, fun hle => hac ?_⟩
  · have heA : e ∈ Q ⊓ QB Y := ⟨hC.le he, hCY he⟩
    refine ⟨heA, ?_⟩
    by_cases he1 : e = 1
    · rw [he1]; exact (Vt _ _ _ _ _).one_mem
    · obtain ⟨gC, hgC⟩ := hC.conj
      refine D.ht.mem_Vt_of_isRoot D.h34 D.hspread D.H D.hs heA
        ⟨gC, gC⁻¹ * e * gC, mem_conjSubgroup.mp (hgC ▸ he), fun h0 => he1 ?_, by group⟩
      calc e = gC * (gC⁻¹ * e * gC) * gC⁻¹ := by group
        _ = 1 := by rw [h0]; group
  · exact Subgroup.mem_centralizer_singleton_iff.mp (hle haC)

private def commHomOfLe (hc : Ctx M Q Z B) {c : G} (hcQ : c ∈ Q) (A : Subgroup G)
    (hA : A ≤ Q) : ↥A →* ↥Z where
  toFun a := ⟨⁅(a : G), c⁆, comm_mem_Z hc.hyp (hA a.2) hcQ⟩
  map_one' := Subtype.ext (by simp [commutatorElement_def])
  map_mul' a b := by
    refine Subtype.ext ?_
    have haQ : (a : G) ∈ Q := hA a.2
    have hbQ : (b : G) ∈ Q := hA b.2
    have hbZ : ⁅(b : G), c⁆ ∈ Z := comm_mem_Z hc.hyp hbQ hcQ
    have hconj : (a : G) * ⁅(b : G), c⁆ * (a : G)⁻¹ = ⁅(b : G), c⁆ := by
      rw [← Z_central hc.hyp hbZ haQ]
      group
    have e : ⁅((a : G) * b), c⁆ = ⁅(b : G), c⁆ * ⁅(a : G), c⁆ := by
      rw [show ⁅((a : G) * b), c⁆ =
        (a : G) * ⁅(b : G), c⁆ * (a : G)⁻¹ * ⁅(a : G), c⁆ by
        simp only [commutatorElement_def]; group, hconj]
    show ⁅((a : G) * b), c⁆ = ⁅(a : G), c⁆ * ⁅(b : G), c⁆
    rw [e, Z_central hc.hyp hbZ (hc.hyp.Z_normal.1 (comm_mem_Z hc.hyp haQ hcQ))]

private theorem ker_commHomOfLe (hc : Ctx M Q Z B) {c : G} (hcQ : c ∈ Q)
    (A : Subgroup G) (hA : A ≤ Q) :
    (commHomOfLe hc hcQ A hA).ker =
      (A ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact ⟨a.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h))⟩
  · rintro ⟨-, ha⟩
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp ha))

theorem BadA.card_le_card_centralizer (D : BadA hc n t Y) {c : G} (hcQ : c ∈ Q)
    {X : Subgroup G} (hX : Ctx M Q Z X) (hXV : X ≤ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t)
    (hXc : ¬ X ≤ Subgroup.centralizer ({c} : Set G)) :
    Nat.card Z * Nat.card ↥(Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ⊓
      Subgroup.centralizer ({c} : Set G)) ≤
    Nat.card ↥(Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G)) := by
  let A : Subgroup G := Q ⊓ QB Y
  let A₀ : Subgroup G := A ⊓ Vt M (LB M Q B) B Z t
  let C : Subgroup G := Subgroup.centralizer ({c} : Set G)
  change Nat.card Z * Nat.card ↥(A₀ ⊓ C) ≤ Nat.card ↥(A ⊓ C)
  obtain ⟨m, -, hA₀card, hAcard⟩ := D.card
  have hA₀leQ : A₀ ≤ Q := inf_le_left.trans inf_le_left
  have hAleQ : A ≤ Q := inf_le_left
  have hsurj : Function.Surjective (commHomOfLe hc hcQ A₀ hA₀leQ) := by
    intro z
    obtain ⟨b, hbX, hbc⟩ := SetLike.not_le_iff_exists.mp hXc
    have hbc' : b * c ≠ c * b := fun h =>
      hbc (Subgroup.mem_centralizer_singleton_iff.mpr h)
    obtain ⟨β, hβX, hβ⟩ := hX.exists_mem_comm_eq hbX hcQ hbc' z.2
    exact ⟨⟨β, hXV hβX⟩, Subtype.ext hβ⟩
  have hker₀ : Nat.card (commHomOfLe hc hcQ A₀ hA₀leQ).ker = Nat.card ↥(A₀ ⊓ C) := by
    rw [ker_commHomOfLe]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A₀ ⊓ C ≤ A₀)).toEquiv
  have hcard₀ : Nat.card ↥(A₀ ⊓ C) * Nat.card Z = Nat.card Z ^ m := by
    rw [← hker₀, Subgroup.card_ker_mul_card_of_surjective hsurj]
    exact hA₀card
  have hker : Nat.card (commHomOfLe hc hcQ A hAleQ).ker = Nat.card ↥(A ⊓ C) := by
    rw [ker_commHomOfLe]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ C ≤ A)).toEquiv
  let φ : ↥A →* ↥Z := commHomOfLe hc hcQ A hAleQ
  have h1 : Nat.card Z ^ (m + 1) ≤ Nat.card φ.ker * Nat.card Z := by
    calc Nat.card Z ^ (m + 1) ≤ Nat.card ↥A := hAcard
      _ = Nat.card φ.ker * Nat.card φ.range := (Subgroup.card_ker_mul_card_range _).symm
      _ ≤ Nat.card φ.ker * Nat.card Z := Nat.mul_le_mul_left _
          (Subgroup.card_le_card_group (H := φ.range))
  rw [pow_succ] at h1
  have h3 : Nat.card Z ^ m ≤ Nat.card φ.ker := Nat.le_of_mul_le_mul_right h1 Nat.card_pos
  rw [hker] at h3
  calc Nat.card Z * Nat.card ↥(A₀ ⊓ C)
      = Nat.card ↥(A₀ ⊓ C) * Nat.card Z := Nat.mul_comm _ _
    _ = Nat.card Z ^ m := hcard₀
    _ ≤ Nat.card ↥(A ⊓ C) := h3

theorem BadA.exists_adm (D : BadA hc n t Y) :
    ∃ c : G, Adm103 M Q Z B t Y c ∧ ∃ X : Subgroup G, Ctx M Q Z X ∧
      X ≤ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ∧ Y ≤ QB X ∧
        ¬ X ≤ Subgroup.centralizer ({c} : Set G) := by
  obtain ⟨α, hαA, hαV⟩ := SetLike.not_le_iff_exists.mp D.hbad
  obtain ⟨c, hcQ, hcα, hcB, hcW⟩ :=
    Good101.exists_mem_centralizer_not_mem_Wt D.H D.ht hαA.1 hαV
  obtain ⟨X, hX, hXV, hYX, hXc⟩ := D.exists_root_group_of_not_mem_Wt hcQ hcW
  exact ⟨c, ⟨hcQ, hcB, hcW,
    ⟨α, ⟨hαA, Subgroup.mem_centralizer_singleton_iff.mpr hcα.symm⟩, hαV⟩,
    D.card_le_card_centralizer hcQ hX hXV hXc⟩, X, hX, hXV, hYX, hXc⟩

private theorem BadA.exists_shift_centralizer (D : BadA hc n t Y) {c c₀ : G}
    (hAc₀ : ∀ a ∈ Q ⊓ QB Y, a * c₀ = c₀ * a) :
    Q ⊓ QB Y ⊓ Subgroup.centralizer ({c * c₀} : Set G) =
      Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G) ∧
    Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ⊓ Subgroup.centralizer ({c * c₀} : Set G) =
      Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ⊓ Subgroup.centralizer ({c} : Set G) := by
  have hiff : ∀ a ∈ Q ⊓ QB Y, (a ∈ Subgroup.centralizer ({c * c₀} : Set G) ↔
      a ∈ Subgroup.centralizer ({c} : Set G)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    have h0 := hAc₀ a ha
    constructor
    · intro h
      have h' : a * c * c₀ = c * a * c₀ := by
        calc a * c * c₀ = a * (c * c₀) := by group
          _ = c * c₀ * a := h
          _ = c * (c₀ * a) := by group
          _ = c * (a * c₀) := by rw [h0]
          _ = c * a * c₀ := by group
      exact mul_right_cancel h'
    · intro h
      calc a * (c * c₀) = (a * c) * c₀ := by group
        _ = (c * a) * c₀ := by rw [h]
        _ = c * (a * c₀) := by group
        _ = c * (c₀ * a) := by rw [h0]
        _ = c * c₀ * a := by group
  have hCeq : Q ⊓ QB Y ⊓ Subgroup.centralizer ({c * c₀} : Set G) =
      Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G) := by
    ext a
    exact ⟨fun ⟨ha, hac⟩ => ⟨ha, (hiff a ha).mp hac⟩,
      fun ⟨ha, hac⟩ => ⟨ha, (hiff a ha).mpr hac⟩⟩
  have hCeq0 : Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ⊓ Subgroup.centralizer ({c * c₀} : Set G) =
      Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t ⊓ Subgroup.centralizer ({c} : Set G) := by
    ext a
    exact ⟨fun ⟨ha, hac⟩ => ⟨ha, (hiff a ha.1).mp hac⟩,
      fun ⟨ha, hac⟩ => ⟨ha, (hiff a ha.1).mpr hac⟩⟩
  exact ⟨hCeq, hCeq0⟩

theorem BadA.exists_shift (D : BadA hc n t Y) {c : G} (hc' : Adm103 M Q Z B t Y c) {b : G}
    (hb : b ∈ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t) :
    ∃ c' : G, Adm103 M Q Z B t Y c' ∧
      Q ⊓ QB Y ⊓ Subgroup.centralizer ({c'} : Set G) =
        Q ⊓ QB Y ⊓ Subgroup.centralizer ({c} : Set G) ∧
      ∃ z ∈ Z, ⁅t, c'⁆ = ⁅t, c⁆ * b * z := by
  have ht2 : t * t = 1 := D.hs.x_sq
  obtain ⟨c₀, hc₀W, hc₀⟩ :=
    hc.exists_comm_mul_inv_mem_Z_of_mem_Tt D.ht.mem_LB (D.ht.Vt_le_Ut D.h34 D.H)
      (D.ht.Vt_le_Tt D.h34 D.H hb.2)
  have hc₀Q : c₀ ∈ Q := hc₀W.1
  have hb2 : b * b = 1 := D.mul_self_eq_one hb.1
  have hc₀V : ⁅c₀, t⁆ ∈ Vt M (LB M Q B) B Z t := by
    have e : ⁅c₀, t⁆ = (⁅c₀, t⁆ * b⁻¹) * b := by group
    rw [e]
    exact (Vt _ _ _ _ _).mul_mem (sec39_Z_le_Vt hc₀) hb.2
  have hAc₀ : ∀ a ∈ Q ⊓ QB Y, a * c₀ = c₀ * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (hc.Tt_le_centralizer_of_comm_mem D.ht.mem_LB ht2 hc₀Q hc₀V (D.inf_QB_le_Tt ha))
  obtain ⟨hCeq, hCeq0⟩ := D.exists_shift_centralizer hAc₀
  have hBV : B ≤ Vt M (LB M Q B) B Z t := by
    have h := sec39_conjB_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z) M.one_mem
      (by rw [conjSubgroup_one]; exact D.ht.mem_LB)
    rwa [conjSubgroup_one] at h
  have hc₀B : c₀ ∈ Subgroup.centralizer (B : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBV) hc₀W.2
  refine ⟨c * c₀, ⟨Q.mul_mem hc'.mem hc₀Q,
    (Subgroup.centralizer (B : Set G)).mul_mem hc'.centB hc₀B, fun hW => hc'.notW ?_,
    by rw [hCeq]; exact hc'.exα, by rw [hCeq, hCeq0]; exact hc'.card⟩, hCeq,
    ⁅b, c⁆ * (⁅c₀, t⁆ * b⁻¹)⁻¹, Z.mul_mem (comm_mem_Z hc.hyp hb.1.1 hc'.mem) (Z.inv_mem hc₀), ?_⟩
  · have h' := (Wt Q _).mul_mem hW ((Wt Q _).inv_mem hc₀W)
    rwa [mul_inv_cancel_right] at h'
  · have hcζ : c * (⁅c₀, t⁆ * b⁻¹)⁻¹ * c⁻¹ = (⁅c₀, t⁆ * b⁻¹)⁻¹ := by
      rw [← Z_central hc.hyp (Z.inv_mem hc₀) hc'.mem]; group
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have hc₀t : ⁅t, c₀⁆ = b⁻¹ * (⁅c₀, t⁆ * b⁻¹)⁻¹ := by
      rw [← commutatorElement_inv c₀ t]; group
    calc ⁅t, c * c₀⁆ = ⁅t, c⁆ * (c * ⁅t, c₀⁆ * c⁻¹) := by simp only [commutatorElement_def]; group
      _ = ⁅t, c⁆ * ((c * b⁻¹ * c⁻¹) * (c * (⁅c₀, t⁆ * b⁻¹)⁻¹ * c⁻¹)) := by rw [hc₀t]; group
      _ = ⁅t, c⁆ * ((b⁻¹ * ⁅b, c⁆) * (⁅c₀, t⁆ * b⁻¹)⁻¹) := by
          rw [hcζ, show c * b⁻¹ * c⁻¹ = b⁻¹ * ⁅b, c⁆ by simp only [commutatorElement_def]; group]
      _ = ⁅t, c⁆ * b * (⁅b, c⁆ * (⁅c₀, t⁆ * b⁻¹)⁻¹) := by rw [hbinv]; group

end CFSG.RankThree.GF2n.Stroth80
