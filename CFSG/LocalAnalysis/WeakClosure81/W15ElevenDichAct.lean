module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenS4B
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenSeven
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenDichAut

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem comm_sq_of_mem_elemFamilyIn_two {A T : Subgroup G} (hA : A ∈ elemFamilyIn 2 T) :
    A ≤ T ∧ (∀ a a' : ↥A, a * a' = a' * a) ∧ ∀ a : ↥A, a * a = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAT, hel, -⟩ := mem_elemFamilyIn.1 hA
  haveI := hel
  refine ⟨hAT, fun a a' => mul_comm' a a', fun a => ?_⟩
  have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) (a : G) a.2
  exact Subtype.ext (by simpa [pow_two] using h)

private theorem b15_DichAct_relIndex_sup {A B : Subgroup G}
    (h : B ≤ normalizer (A : Set G)) : B.relIndex (A ⊔ B) = B.relIndex A := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)) ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE B
    (le_sup_left : A ≤ A ⊔ B)).injective, ?_⟩
  intro q
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hy' : y ∈ (A : Set G) * (B : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left A B h) ▸ hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simpa using hb

private def b15_DichAct_conjAut {X : Subgroup G} {v : G} (hv : v ∈ normalizer (X : Set G))
    (hvv : v * v = 1) : MulAut ↥X where
  toFun y := ⟨v * y * v⁻¹, (Subgroup.mem_normalizer_iff.1 hv y).1 y.2⟩
  invFun y := ⟨v * y * v⁻¹, (Subgroup.mem_normalizer_iff.1 hv y).1 y.2⟩
  left_inv y := by
    apply Subtype.ext
    have h : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
    show v * (v * (y : G) * v⁻¹) * v⁻¹ = y
    rw [h]
    calc v * (v * (y : G) * v) * v = (v * v) * y * (v * v) := by group
      _ = y := by rw [hvv]; group
  right_inv y := by
    apply Subtype.ext
    have h : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
    show v * (v * (y : G) * v⁻¹) * v⁻¹ = y
    rw [h]
    calc v * (v * (y : G) * v) * v = (v * v) * y * (v * v) := by group
      _ = y := by rw [hvv]; group
  map_mul' a b := by
    apply Subtype.ext
    show v * ((a : G) * b) * v⁻¹ = v * a * v⁻¹ * (v * b * v⁻¹)
    group

private theorem b15_DichAct_aut_inv {p : ℕ} [Fact p.Prime] {N : Type*} [Group N] [Finite N]
    (hcard : Nat.card N = p) (hp2 : p ≠ 2) (σ : MulAut N) (hσσ : σ * σ = 1) (hσ : σ ≠ 1) :
    ∀ y : N, σ y = y⁻¹ := by
  haveI : IsCyclic N := isCyclic_of_prime_card hcard
  let τ : MulAut N :=
    { toFun := fun y => y⁻¹
      invFun := fun y => y⁻¹
      left_inv := inv_inv
      right_inv := inv_inv
      map_mul' := fun a b => by rw [mul_inv_rev, mul_comm' b⁻¹ a⁻¹] }
  have hττ : τ * τ = 1 := MulEquiv.ext fun y => inv_inv y
  have hτ : τ ≠ 1 := by
    intro h
    have hnt : Nontrivial N := Finite.one_lt_card_iff_nontrivial.1 (by
      rw [hcard]; exact (Fact.out : p.Prime).one_lt)
    obtain ⟨y, hy⟩ := exists_ne (1 : N)
    have hyy : y⁻¹ = y := MulEquiv.congr_fun h y
    have hy2 : y ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← hyy]
      exact inv_mul_cancel y
    have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
    have h2 : orderOf y ∣ p := hcard ▸ orderOf_dvd_natCard y
    have h3 : orderOf y ≠ 1 := fun h' => hy (orderOf_eq_one_iff.1 h')
    have h4 : orderOf y = 2 := ((Nat.dvd_prime Nat.prime_two).1 h1).resolve_left h3
    rw [h4] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).1 h2).symm
  have h := mulAut_eq_of_card_prime hcard σ τ hσσ hττ hσ hτ
  intro y
  exact MulEquiv.congr_fun h y

section Action

variable {Q I B : Subgroup G}

private def b15_DichAct_conjOn (hBQ : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) (b : B) : Q →* Q where
  toFun q := ⟨(b : G) * q * (b : G)⁻¹, hBQ b b.2 q q.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]

private noncomputable def b15_DichAct_conjQuot [(I.subgroupOf Q).Normal]
    (hBQ : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) (hBI : ∀ b ∈ B, ∀ i ∈ I, b * i * b⁻¹ ∈ I)
    (b : B) : (Q ⧸ I.subgroupOf Q) →* (Q ⧸ I.subgroupOf Q) :=
  QuotientGroup.map (I.subgroupOf Q) (I.subgroupOf Q) (b15_DichAct_conjOn hBQ b) (fun x hx =>
    Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 (hBI b b.2 x (Subgroup.mem_subgroupOf.1 hx))))

private theorem b15_DichAct_conjQuot_mul [(I.subgroupOf Q).Normal]
    (hBQ : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) (hBI : ∀ b ∈ B, ∀ i ∈ I, b * i * b⁻¹ ∈ I)
    (b b' : B) (y : Q ⧸ I.subgroupOf Q) :
    b15_DichAct_conjQuot hBQ hBI (b * b') y =
      b15_DichAct_conjQuot hBQ hBI b (b15_DichAct_conjQuot hBQ hBI b' y) := by
  induction y using QuotientGroup.induction_on with
  | H q =>
    change QuotientGroup.mk (b15_DichAct_conjOn hBQ (b * b') q) =
      QuotientGroup.mk (b15_DichAct_conjOn hBQ b (b15_DichAct_conjOn hBQ b' q))
    congr 1
    ext
    simp [b15_DichAct_conjOn, mul_assoc]

private theorem b15_DichAct_conjQuot_one [(I.subgroupOf Q).Normal]
    (hBQ : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) (hBI : ∀ b ∈ B, ∀ i ∈ I, b * i * b⁻¹ ∈ I)
    (y : Q ⧸ I.subgroupOf Q) : b15_DichAct_conjQuot hBQ hBI 1 y = y := by
  induction y using QuotientGroup.induction_on with
  | H q =>
    change QuotientGroup.mk (b15_DichAct_conjOn hBQ 1 q) = QuotientGroup.mk q
    congr 1
    ext
    simp [b15_DichAct_conjOn]

private theorem b15_DichAct_exists_action [(I.subgroupOf Q).Normal]
    (hBQ : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) (hBI : ∀ b ∈ B, ∀ i ∈ I, b * i * b⁻¹ ∈ I) :
    ∃ ρ : B →* MulAut (Q ⧸ I.subgroupOf Q), ∀ (b : B) (q : Q),
      ρ b (QuotientGroup.mk q) =
        QuotientGroup.mk ⟨(b : G) * q * (b : G)⁻¹, hBQ b b.2 q q.2⟩ :=
  ⟨{ toFun := fun b =>
        { toFun := b15_DichAct_conjQuot hBQ hBI b
          invFun := b15_DichAct_conjQuot hBQ hBI b⁻¹
          left_inv := fun y => by
            rw [← b15_DichAct_conjQuot_mul, inv_mul_cancel, b15_DichAct_conjQuot_one]
          right_inv := fun y => by
            rw [← b15_DichAct_conjQuot_mul, mul_inv_cancel, b15_DichAct_conjQuot_one]
          map_mul' := (b15_DichAct_conjQuot hBQ hBI b).map_mul }
     map_one' := MulEquiv.ext (b15_DichAct_conjQuot_one hBQ hBI)
     map_mul' := fun b b' => MulEquiv.ext (b15_DichAct_conjQuot_mul hBQ hBI b b') },
    fun _ _ => rfl⟩

end Action

namespace Cfg1511

variable {M V₀ V U S H P Q₀ X : Subgroup G} {p : ℕ} {v : G}

theorem tSub15_le_normalizer_iHull15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    tSub15 M V₀ V U P ≤ normalizer (iHull15 V₀ U H : Set G) :=
  c.tSub15_le_H.trans (Hyp1510.le_normalizer_iHull15 V₀ U H)

theorem isPGroup_two_tSub15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    IsPGroup 2 ↥(tSub15 M V₀ V U P) :=
  c.hyp.sylow.isPGroup.to_le (tSub15_le_P M V₀ V U P)

theorem qSub15_le_centralizer_iHull15
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) :
    qSub15 M V₀ V U H P ≤ centralizer (iHull15 V₀ U H : Set G) := by
  haveI : IsMulCommutative (iHull15 V₀ U H) := c.isElemAbelian_iHull15.1
  rw [c.qSub15_eq_sup hX]
  refine sup_le (Subgroup.le_centralizer (iHull15 V₀ U H)) ?_
  exact (cSub15_le_centralizer M V₀ V U H P).trans
    (Subgroup.centralizer_le (Hyp1510.iHull15_le_kHull15 V₀ U H))

theorem not_mem_qSub15 (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) : v ∉ qSub15 M V₀ V U H P := by
  intro hv
  have h : v ∈ qSub15 M V₀ V U H P ⊓ kHull15 V₀ H := ⟨hv, Hyp1510.V₀_le_kHull15 V₀ H hX.mem⟩
  rw [c.qSub15_inf_kHull15] at h
  exact hX.not_mem h

theorem exists_equiv_quot [((iHull15 V₀ U H).subgroupOf Q₀).Normal]
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) :
    ∃ φ : ↥X →* (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀), Function.Bijective φ ∧
      ∀ x : ↥X, φ x = QuotientGroup.mk ⟨(x : G), hX.le x.2⟩ := by
  refine ⟨(QuotientGroup.mk' ((iHull15 V₀ U H).subgroupOf Q₀)).comp (Subgroup.inclusion hX.le),
    ⟨?_, ?_⟩, fun x => rfl⟩
  · refine (injective_iff_map_eq_one _).2 fun x hx => ?_
    have h1 : (Subgroup.inclusion hX.le x : ↥Q₀) ∈ (iHull15 V₀ U H).subgroupOf Q₀ :=
      (QuotientGroup.eq_one_iff _).1 hx
    have h2 : (x : G) ∈ X ⊓ iHull15 V₀ U H := ⟨x.2, Subgroup.mem_subgroupOf.1 h1⟩
    rw [hX.inf_eq] at h2
    exact Subtype.ext (Subgroup.mem_bot.1 h2)
  · intro n
    induction n using QuotientGroup.induction_on with
    | H q =>
      have hXN : X ≤ normalizer (iHull15 V₀ U H : Set G) :=
        (hX.le_H c).trans (Hyp1510.le_normalizer_iHull15 V₀ U H)
      have hq : (q : G) ∈ (↑(X ⊔ iHull15 V₀ U H) : Set G) := by
        rw [hX.sup_eq]
        exact q.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right X (iHull15 V₀ U H) hXN] at hq
      obtain ⟨x, hx, i, hi, hxi⟩ := hq
      refine ⟨⟨x, hx⟩, ?_⟩
      change (QuotientGroup.mk (Subgroup.inclusion hX.le ⟨x, hx⟩) :
        ↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) = QuotientGroup.mk q
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h3 : x⁻¹ * (q : G) = i := by rw [← hxi]; group
      simpa [h3] using hi

theorem card_quot_eq_card_X [((iHull15 V₀ U H).subgroupOf Q₀).Normal]
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) :
    Nat.card (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) = Nat.card ↥X := by
  obtain ⟨φ, hφ, -⟩ := c.exists_equiv_quot hX
  exact (Nat.card_congr (Equiv.ofBijective φ hφ)).symm

theorem card_X_eq_p_or_pow_three (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) : Nat.card ↥X = p ∨ Nat.card ↥X = p ^ 3 := by
  haveI : ((iHull15 V₀ U H).subgroupOf Q₀).Normal := c.normal_subgroupOf
  have h : (iHull15 V₀ U H).relIndex Q₀ = Nat.card ↥X := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact c.card_quot_eq_card_X hX
  rw [← h]
  exact c.relIndex_eq

theorem isExtraspecial_quot [((iHull15 V₀ U H).subgroupOf Q₀).Normal]
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) (hcard : Nat.card ↥X = p ^ 3) :
    CFSG.IsExtraspecial p (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) := by
  have hcardN : Nat.card (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) = p ^ 3 :=
    (c.card_quot_eq_card_X hX).trans hcard
  have hshape := c.shape
  simp only [OddCoreShape15] at hshape
  rcases hshape with h | ⟨-, h, -⟩
  · exfalso
    rw [hcardN] at h
    have h3 : p ^ 3 = p ^ 1 := by simpa using h
    have := Nat.pow_right_injective c.prime.two_le h3
    omega
  · exact h

theorem exists_action_tSub15 [((iHull15 V₀ U H).subgroupOf Q₀).Normal]
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) :
    ∃ ρ : ↥(tSub15 M V₀ V U P) →* MulAut (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀),
      (∀ (t : ↥(tSub15 M V₀ V U P)) (q : ↥Q₀), ∃ q' : ↥Q₀,
        (q' : G) = (t : G) * q * (t : G)⁻¹ ∧ ρ t (QuotientGroup.mk q) = QuotientGroup.mk q') ∧
      ∀ t : ↥(tSub15 M V₀ V U P), ρ t = 1 → (t : G) ∈ qSub15 M V₀ V U H P := by
  have hTH : tSub15 M V₀ V U P ≤ H := c.tSub15_le_H
  have hHI : H ≤ normalizer (iHull15 V₀ U H : Set G) := Hyp1510.le_normalizer_iHull15 V₀ U H
  have hBQ : ∀ b ∈ tSub15 M V₀ V U P, ∀ q ∈ Q₀, b * q * b⁻¹ ∈ Q₀ := fun b hb q hq =>
    (Subgroup.mem_normalizer_iff.1 (c.odd.normal (hTH hb)) q).1 hq
  have hBI : ∀ b ∈ tSub15 M V₀ V U P, ∀ i ∈ iHull15 V₀ U H, b * i * b⁻¹ ∈ iHull15 V₀ U H :=
    fun b hb i hi => (Subgroup.mem_normalizer_iff.1 (hHI (hTH hb)) i).1 hi
  obtain ⟨ρ, hρ⟩ := b15_DichAct_exists_action (Q := Q₀) (I := iHull15 V₀ U H)
    (B := tSub15 M V₀ V U P) hBQ hBI
  refine ⟨ρ, fun t q => ⟨⟨(t : G) * q * (t : G)⁻¹, hBQ t t.2 q q.2⟩, rfl, hρ t q⟩, ?_⟩
  intro t ht1
  refine c.mem_qSub15_of_commutator_mem hX t.2 ?_
  have hQ : ∀ q ∈ Q₀, ⁅q, (t : G)⁆ ∈ iHull15 V₀ U H := by
    intro q hq
    have h1 := hρ t ⟨(q : G)⁻¹, Q₀.inv_mem hq⟩
    rw [ht1, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    simpa [commutatorElement_def, mul_assoc] using h1
  have hV : ∀ w ∈ V₀, ⁅w, (t : G)⁆ ∈ iHull15 V₀ U H := by
    intro w hw
    have htC : (t : G) ∈ F11.CTilde M V₀ V := tSub15_le_cTilde M V₀ V U P t.2
    have hwV : w ∈ V := c.cex.hyp.h6.le hw
    have h1 : ⁅(t : G), w⁆ ∈ v1Sub15 V₀ U :=
      c.cex.commutator_cTilde_le_v1Sub15 c.inputs c.std
        (Subgroup.commutator_mem_commutator htC hwV)
    rw [← commutatorElement_inv]
    exact (iHull15 V₀ U H).inv_mem (Hyp1510.v1Sub15_le_iHull15 V₀ U H h1)
  intro k hk
  obtain ⟨q, hq, w, hw, rfl⟩ := c.exists_mul_of_mem_kHull15 hk
  have hqH : q ∈ H := c.hyp.kHull15_le (c.odd.le_kHull hq)
  have key : ⁅q * w, (t : G)⁆ = q * ⁅w, (t : G)⁆ * q⁻¹ * ⁅q, (t : G)⁆ := by
    simp only [commutatorElement_def]; group
  rw [key]
  exact (iHull15 V₀ U H).mul_mem
    ((Subgroup.mem_normalizer_iff.1 (hHI hqH) _).1 (hV w hw)) (hQ q hq)

theorem mk_mem_center_quot [((iHull15 V₀ U H).subgroupOf Q₀).Normal]
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) {z : G} (hzX : z ∈ X)
    (hzc : ∀ x ∈ X, z * x = x * z) :
    (QuotientGroup.mk (⟨z, hX.le hzX⟩ : ↥Q₀) : ↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) ∈
      Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) := by
  obtain ⟨φ, hφ, hφx⟩ := c.exists_equiv_quot hX
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨x, rfl⟩ := hφ.2 y
  rw [hφx x, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hzc x x.2).symm

theorem center_eq_zpowers_mk [((iHull15 V₀ U H).subgroupOf Q₀).Normal]
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) (hcard : Nat.card ↥X = p ^ 3)
    {z : G} (hzX : z ∈ X) (hzc : ∀ x ∈ X, z * x = x * z) (hz1 : z ≠ 1) :
    Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) =
      Subgroup.zpowers (QuotientGroup.mk (⟨z, hX.le hzX⟩ : ↥Q₀) :
        ↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) := by
  haveI := c.isExtraspecial_quot hX hcard
  obtain ⟨φ, hφ, hφx⟩ := c.exists_equiv_quot hX
  have hmem := c.mk_mem_center_quot hX hzX hzc
  have hne : (QuotientGroup.mk (⟨z, hX.le hzX⟩ : ↥Q₀) :
      ↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) ≠ 1 := by
    intro h
    have h1 : φ ⟨z, hzX⟩ = φ 1 := by rw [hφx, map_one]; exact h
    have h2 : (⟨z, hzX⟩ : ↥X) = 1 := hφ.1 h1
    exact hz1 (congrArg Subtype.val h2)
  have hle : Subgroup.zpowers (QuotientGroup.mk (⟨z, hX.le hzX⟩ : ↥Q₀) :
      ↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) ≤
      Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) := (Subgroup.zpowers_le).2 hmem
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hZcard : Nat.card (Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀)) = p :=
    CFSG.IsExtraspecial.center_order_p p _
  have hdvd : Nat.card (Subgroup.zpowers (QuotientGroup.mk (⟨z, hX.le hzX⟩ : ↥Q₀) :
      ↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀)) ∣ p :=
    (Subgroup.card_dvd_of_le hle).trans (dvd_of_eq hZcard)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rcases (Nat.dvd_prime c.prime).1 hdvd with h1 | h1
  · exfalso
    have hbot := Subgroup.card_eq_one.1 h1
    have hmem1 := Subgroup.mem_zpowers (QuotientGroup.mk (⟨z, hX.le hzX⟩ : ↥Q₀) :
      ↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀)
    rw [hbot, Subgroup.mem_bot] at hmem1
    exact hne hmem1
  · rw [hZcard, h1]

theorem exists_generator_inv (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v)
    (hcard : Nat.card ↥X = p) :
    ∃ x ∈ X, x ≠ 1 ∧ x ^ p = 1 ∧ v * x * v⁻¹ = x⁻¹ ∧
      iHull15 V₀ U H ⊓ centralizer ({x} : Set G) = ⊥ := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hvv : v * v = 1 := XData15.mul_self c hX
  let σ : MulAut ↥X := b15_DichAct_conjAut hX.normalizes hvv
  have hσy : ∀ y : ↥X, (σ y : G) = v * y * v⁻¹ := fun y => rfl
  have hσσ : σ * σ = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    show v * (v * (y : G) * v⁻¹) * v⁻¹ = y
    have h : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
    rw [h]
    calc v * (v * (y : G) * v) * v = (v * v) * y * (v * v) := by group
      _ = y := by rw [hvv]; group
  have hσ1 : σ ≠ 1 := by
    intro h
    have hcomm : ∀ x ∈ X, x * v = v * x := by
      intro x hx
      have h1 := congrArg Subtype.val (MulEquiv.congr_fun h ⟨x, hx⟩)
      have h2 : v * x * v⁻¹ = x := h1
      calc x * v = (v * x * v⁻¹) * v := by rw [h2]
        _ = v * x := by group
    have hle : ⁅X, Subgroup.zpowers v⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro x hx w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      have hc : Commute x v := hcomm x hx
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (hc.zpow_right n).eq
    rw [hX.comm_eq] at hle
    have h1 : Nat.card ↥X = 1 := Subgroup.card_eq_one.2 (le_bot_iff.1 hle)
    rw [hcard] at h1
    exact (Fact.out : p.Prime).one_lt.ne' h1
  have hinv : ∀ y : ↥X, σ y = y⁻¹ := b15_DichAct_aut_inv hcard c.p_ne_two σ hσσ hσ1
  haveI : IsCyclic ↥X := isCyclic_of_prime_card hcard
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥X)
  have hg1 : g ≠ 1 := by
    intro h
    have hnt : Nontrivial ↥X := Finite.one_lt_card_iff_nontrivial.1 (by
      rw [hcard]; exact (Fact.out : p.Prime).one_lt)
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥X)
    have := hg y
    rw [h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
    exact hy this
  have hgpow : ∀ y ∈ X, ∃ n : ℤ, (g : G) ^ n = y := by
    intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨y, hy⟩)
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  refine ⟨(g : G), g.2, fun h => hg1 (Subtype.ext h), ?_, ?_, ?_⟩
  · have h : g ^ p = 1 := hcard ▸ pow_card_eq_one'
    simpa using congrArg Subtype.val h
  · exact congrArg Subtype.val (hinv g)
  · refine eq_bot_iff.2 (le_trans ?_ hX.cent.le)
    intro y hy
    refine ⟨hy.1, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    obtain ⟨n, rfl⟩ := hgpow z hz
    have hyc : Commute (g : G) y := Subgroup.mem_centralizer_iff.1 hy.2 (g : G) rfl
    exact (hyc.zpow_left n).eq

theorem card_kHull15_eq (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) :
    Nat.card ↥(kHull15 V₀ H) = 2 * Nat.card ↥X * Nat.card ↥(iHull15 V₀ U H) := by
  haveI : ((iHull15 V₀ U H).subgroupOf Q₀).Normal := c.normal_subgroupOf
  have h1 := Subgroup.relIndex_mul_card Q₀ (kHull15 V₀ H)
  rw [inf_eq_left.2 c.odd.le_kHull, c.relIndex_Q₀_kHull15] at h1
  have h2 := Subgroup.relIndex_mul_card (iHull15 V₀ U H) Q₀
  rw [inf_eq_left.2 c.odd.iHull_le] at h2
  have h3 : (iHull15 V₀ U H).relIndex Q₀ = Nat.card ↥X := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact c.card_quot_eq_card_X hX
  rw [h3] at h2
  rw [← h1, ← h2, mul_assoc]

theorem card_mul_card_inf_qSub15_le
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) {A : Subgroup G}
    (hA : A ∈ elemFamilyIn 2 (tSub15 M V₀ V U P)) :
    Nat.card ↥(iHull15 V₀ U H) * Nat.card ↥(A ⊓ qSub15 M V₀ V U H P) ≤
      Nat.card ↥A * Nat.card ↥(iHull15 V₀ U H ⊓ centralizer (A : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAT, hAcomm, -⟩ := comm_sq_of_mem_elemFamilyIn_two hA
  obtain ⟨-, hAel, hAcard⟩ := mem_elemFamilyIn.1 hA
  have hAe : IsElemAbelian 2 A := isElemAbelian_iff_isElementaryAbelian.2 hAel
  have hIe : IsElemAbelian 2 (iHull15 V₀ U H) := c.isElemAbelian_iHull15
  have hQC := c.qSub15_le_centralizer_iHull15 hX
  have hSe : IsElemAbelian 2 (A ⊓ qSub15 M V₀ V U H P) := hAe.mono inf_le_left
  have hcomm : ∀ a ∈ iHull15 V₀ U H, ∀ b ∈ A ⊓ qSub15 M V₀ V U H P, a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.1 (hQC hb.2) a ha
  have hBe := hIe.sup_of_commute hSe hcomm
  have hBT : iHull15 V₀ U H ⊔ A ⊓ qSub15 M V₀ V U H P ≤ tSub15 M V₀ V U P :=
    sup_le c.iHull15_le_tSub15 (inf_le_left.trans hAT)
  have hBcard : Nat.card ↥(iHull15 V₀ U H ⊔ A ⊓ qSub15 M V₀ V U H P) ≤ Nat.card ↥A := by
    rw [hAcard]
    exact card_le_pow_pRank_of_le hBT (isElemAbelian_iff_isElementaryAbelian.1 hBe)
  have hSN : A ⊓ qSub15 M V₀ V U H P ≤ normalizer (iHull15 V₀ U H : Set G) :=
    inf_le_left.trans (hAT.trans c.tSub15_le_normalizer_iHull15)
  have hrel := b15_DichAct_relIndex_sup hSN
  have h1 := Subgroup.relIndex_mul_card (A ⊓ qSub15 M V₀ V U H P)
    (iHull15 V₀ U H ⊔ A ⊓ qSub15 M V₀ V U H P)
  have hSB : A ⊓ qSub15 M V₀ V U H P ≤ iHull15 V₀ U H ⊔ A ⊓ qSub15 M V₀ V U H P := le_sup_right
  rw [inf_eq_left.2 hSB, hrel] at h1
  have h2 := Subgroup.relIndex_mul_card (A ⊓ qSub15 M V₀ V U H P) (iHull15 V₀ U H)
  have hleI : A ⊓ qSub15 M V₀ V U H P ⊓ iHull15 V₀ U H ≤
      iHull15 V₀ U H ⊓ centralizer (A : Set G) := by
    intro y hy
    refine ⟨hy.2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    exact congrArg Subtype.val (hAcomm ⟨h, hh⟩ ⟨y, hy.1.1⟩)
  have hcI := Subgroup.card_le_of_le hleI
  calc Nat.card ↥(iHull15 V₀ U H) * Nat.card ↥(A ⊓ qSub15 M V₀ V U H P)
      = Nat.card ↥(A ⊓ qSub15 M V₀ V U H P ⊓ iHull15 V₀ U H) *
          Nat.card ↥(iHull15 V₀ U H ⊔ A ⊓ qSub15 M V₀ V U H P) := by
        rw [← h1, ← h2]; ring
    _ ≤ Nat.card ↥(iHull15 V₀ U H ⊓ centralizer (A : Set G)) * Nat.card ↥A :=
        Nat.mul_le_mul hcI hBcard
    _ = Nat.card ↥A * Nat.card ↥(iHull15 V₀ U H ⊓ centralizer (A : Set G)) := mul_comm _ _

theorem card_iHull15_le_mul_card_inf_centralizer
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) {A : Subgroup G}
    (hA : A ∈ elemFamilyIn 2 (tSub15 M V₀ V U P)) (hAT : A ≤ tSub15 M V₀ V U P)
    {L : Type*} [Group L] (ρ : ↥(tSub15 M V₀ V U P) →* L)
    (hρ : ∀ t : ↥(tSub15 M V₀ V U P), ρ t = 1 → (t : G) ∈ qSub15 M V₀ V U H P) {n : ℕ}
    (hn : (ρ.comp (Subgroup.inclusion hAT)).ker.index ≤ n) :
    Nat.card ↥(iHull15 V₀ U H) ≤ n * Nat.card ↥(iHull15 V₀ U H ⊓ centralizer (A : Set G)) := by
  have h1 := c.card_mul_card_inf_qSub15_le hX hA
  have h2 : Nat.card ↥A ≤ n * Nat.card ↥(A ⊓ qSub15 M V₀ V U H P) :=
    card_le_mul_card_inf_of_index_ker_le (ρ.comp (Subgroup.inclusion hAT))
      (fun a ha => hρ ⟨a, hAT a.2⟩ ha) hn
  have hpos : 0 < Nat.card ↥(A ⊓ qSub15 M V₀ V U H P) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card ↥(iHull15 V₀ U H) * Nat.card ↥(A ⊓ qSub15 M V₀ V U H P)
      ≤ Nat.card ↥A * Nat.card ↥(iHull15 V₀ U H ⊓ centralizer (A : Set G)) := h1
    _ ≤ (n * Nat.card ↥(A ⊓ qSub15 M V₀ V U H P)) *
          Nat.card ↥(iHull15 V₀ U H ⊓ centralizer (A : Set G)) := Nat.mul_le_mul_right _ h2
    _ = (n * Nat.card ↥(iHull15 V₀ U H ⊓ centralizer (A : Set G))) *
          Nat.card ↥(A ⊓ qSub15 M V₀ V U H P) := by ring

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
