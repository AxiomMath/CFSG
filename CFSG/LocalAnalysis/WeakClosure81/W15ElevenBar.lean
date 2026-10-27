module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenFourE
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenBarAut

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Action

variable {Q I B : Subgroup G}

private def b15_Bar_conjOn (hBQ : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) (b : B) : Q →* Q where
  toFun q := ⟨(b : G) * q * (b : G)⁻¹, hBQ b b.2 q q.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]

private noncomputable def b15_Bar_conjQuot [(I.subgroupOf Q).Normal]
    (hBQ : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) (hBI : ∀ b ∈ B, ∀ i ∈ I, b * i * b⁻¹ ∈ I)
    (b : B) : (Q ⧸ I.subgroupOf Q) →* (Q ⧸ I.subgroupOf Q) :=
  QuotientGroup.map (I.subgroupOf Q) (I.subgroupOf Q) (b15_Bar_conjOn hBQ b) (fun x hx =>
    Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 (hBI b b.2 x (Subgroup.mem_subgroupOf.1 hx))))

private theorem b15_Bar_conjQuot_mul [(I.subgroupOf Q).Normal]
    (hBQ : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) (hBI : ∀ b ∈ B, ∀ i ∈ I, b * i * b⁻¹ ∈ I)
    (b b' : B) (y : Q ⧸ I.subgroupOf Q) :
    b15_Bar_conjQuot hBQ hBI (b * b') y =
      b15_Bar_conjQuot hBQ hBI b (b15_Bar_conjQuot hBQ hBI b' y) := by
  induction y using QuotientGroup.induction_on with
  | H q =>
    change QuotientGroup.mk (b15_Bar_conjOn hBQ (b * b') q) =
      QuotientGroup.mk (b15_Bar_conjOn hBQ b (b15_Bar_conjOn hBQ b' q))
    congr 1
    ext
    simp [b15_Bar_conjOn, mul_assoc]

private theorem b15_Bar_conjQuot_one [(I.subgroupOf Q).Normal]
    (hBQ : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) (hBI : ∀ b ∈ B, ∀ i ∈ I, b * i * b⁻¹ ∈ I)
    (y : Q ⧸ I.subgroupOf Q) : b15_Bar_conjQuot hBQ hBI 1 y = y := by
  induction y using QuotientGroup.induction_on with
  | H q =>
    change QuotientGroup.mk (b15_Bar_conjOn hBQ 1 q) = QuotientGroup.mk q
    congr 1
    ext
    simp [b15_Bar_conjOn]

private theorem b15_Bar_exists_action [(I.subgroupOf Q).Normal]
    (hBQ : ∀ b ∈ B, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q) (hBI : ∀ b ∈ B, ∀ i ∈ I, b * i * b⁻¹ ∈ I) :
    ∃ ρ : B →* MulAut (Q ⧸ I.subgroupOf Q), ∀ (b : B) (q : Q),
      ρ b (QuotientGroup.mk q) =
        QuotientGroup.mk ⟨(b : G) * q * (b : G)⁻¹, hBQ b b.2 q q.2⟩ :=
  ⟨{ toFun := fun b =>
        { toFun := b15_Bar_conjQuot hBQ hBI b
          invFun := b15_Bar_conjQuot hBQ hBI b⁻¹
          left_inv := fun y => by
            rw [← b15_Bar_conjQuot_mul, inv_mul_cancel, b15_Bar_conjQuot_one]
          right_inv := fun y => by
            rw [← b15_Bar_conjQuot_mul, mul_inv_cancel, b15_Bar_conjQuot_one]
          map_mul' := (b15_Bar_conjQuot hBQ hBI b).map_mul }
     map_one' := MulEquiv.ext (b15_Bar_conjQuot_one hBQ hBI)
     map_mul' := fun b b' => MulEquiv.ext (b15_Bar_conjQuot_mul hBQ hBI b b') },
    fun _ _ => rfl⟩

end Action

namespace Cfg1511

variable {M V₀ V U S H P Q₀ X : Subgroup G} {p : ℕ} {v : G}

private theorem b15_Bar_exists_equiv [((iHull15 V₀ U H).subgroupOf Q₀).Normal]
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

section Certified


theorem exists_relIndex_le_two_commutator_mem (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) (hXc : Nat.card ↥X = p ^ 3) {Y B : Subgroup G} (hYX : Y ≤ X)
    (hYp : Nat.card ↥Y = p) (hYc : ∀ y ∈ Y, ∀ x ∈ X, y * x = x * y)
    (hBT : B ≤ tSub15 M V₀ V U P) (hBe : IsElemAbelian 2 B)
    (hBY : ⁅B, Y⁆ ≤ iHull15 V₀ U H) :
    ∃ B₀ : Subgroup G, B₀ ≤ B ∧ B₀.relIndex B ≤ 2 ∧
      ∀ b ∈ B₀, ∀ k ∈ kHull15 V₀ H, ⁅k, b⁆ ∈ iHull15 V₀ U H := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  haveI hNorm : ((iHull15 V₀ U H).subgroupOf Q₀).Normal := c.normal_subgroupOf
  have hBH : B ≤ H := hBT.trans c.tSub15_le_H
  have hHI : H ≤ normalizer (iHull15 V₀ U H : Set G) := Hyp1510.le_normalizer_iHull15 V₀ U H
  have hBQ : ∀ b ∈ B, ∀ q ∈ Q₀, b * q * b⁻¹ ∈ Q₀ := fun b hb q hq =>
    (Subgroup.mem_normalizer_iff.1 (c.odd.normal (hBH hb)) q).1 hq
  have hBI : ∀ b ∈ B, ∀ i ∈ iHull15 V₀ U H, b * i * b⁻¹ ∈ iHull15 V₀ U H := fun b hb i hi =>
    (Subgroup.mem_normalizer_iff.1 (hHI (hBH hb)) i).1 hi
  obtain ⟨φ, hφbij, hφ⟩ := b15_Bar_exists_equiv c hX
  have hcardN : Nat.card (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) = p ^ 3 := by
    rw [← hXc]
    exact (Nat.card_congr (Equiv.ofBijective φ hφbij)).symm
  have hshape := c.shape
  simp only [OddCoreShape15] at hshape
  haveI hext : CFSG.IsExtraspecial p (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) := by
    rcases hshape with h | ⟨-, h, -⟩
    · exfalso
      rw [hcardN] at h
      have h3 : p ^ 3 = p ^ 1 := by simpa using h
      have := Nat.pow_right_injective c.prime.two_le h3
      omega
    · exact h
  have hφY : (Y.subgroupOf X).map φ =
      Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro z ⟨y', hy', rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := hφbij.2 g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hYc _ (Subgroup.mem_subgroupOf.1 hy') _ x.2).symm
    · rw [CFSG.IsExtraspecial.center_order_p p _, Subgroup.card_map_of_injective hφbij.1,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv, hYp]
  obtain ⟨ρ, hρ⟩ := b15_Bar_exists_action (Q := Q₀) (I := iHull15 V₀ U H) (B := B) hBQ hBI
  have hZ : ∀ a : ↥B, ∀ z ∈ Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀),
      ρ a z = z := by
    intro a z hz
    rw [← hφY] at hz
    obtain ⟨y', hy', rfl⟩ := hz
    rw [hφ y', hρ, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hy'Y : (y' : G) ∈ Y := Subgroup.mem_subgroupOf.1 hy'
    have h := hBY (Subgroup.commutator_mem_commutator a.2 (Y.inv_mem hy'Y))
    simpa [commutatorElement_def, mul_assoc] using h
  haveI := hBe.1
  have hcomm : ∀ a a' : ↥B, a * a' = a' * a := fun a a' => mul_comm' a a'
  have hsq : ∀ a : ↥B, a * a = 1 := fun a => Subtype.ext (by
    have h := hBe.2 a a.2
    simpa [pow_two] using h)
  have hidx := index_ker_le_two_of_isExtraspecial c.p_ne_two hcardN ρ hcomm hsq hZ
  refine ⟨ρ.ker.map B.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have h : (ρ.ker.map B.subtype).subgroupOf B = ρ.ker :=
      Subgroup.comap_map_eq_self_of_injective B.subtype_injective ρ.ker
    rw [Subgroup.relIndex, h]
    exact hidx
  · intro b hb k hk
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    have hb'1 : ρ b' = 1 := hb'
    have hQ : ∀ q ∈ Q₀, ⁅q, (b' : G)⁆ ∈ iHull15 V₀ U H := by
      intro q hq
      have h1 := hρ b' ⟨(q : G)⁻¹, Q₀.inv_mem hq⟩
      rw [hb'1, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
      simpa [commutatorElement_def, mul_assoc] using h1
    have hV : ∀ w ∈ V₀, ⁅w, (b' : G)⁆ ∈ iHull15 V₀ U H := by
      intro w hw
      have hbC : (b' : G) ∈ F11.CTilde M V₀ V := tSub15_le_cTilde M V₀ V U P (hBT b'.2)
      have hwV : w ∈ V := c.cex.hyp.h6.le hw
      have h1 : ⁅(b' : G), w⁆ ∈ v1Sub15 V₀ U :=
        c.cex.commutator_cTilde_le_v1Sub15 c.inputs c.std
          (Subgroup.commutator_mem_commutator hbC hwV)
      rw [← commutatorElement_inv]
      exact (iHull15 V₀ U H).inv_mem (Hyp1510.v1Sub15_le_iHull15 V₀ U H h1)
    obtain ⟨q, hq, w, hw, rfl⟩ := c.exists_mul_of_mem_kHull15 hk
    have hqH : q ∈ H := c.hyp.kHull15_le (c.odd.le_kHull hq)
    have key : ⁅q * w, (b' : G)⁆ = q * ⁅w, (b' : G)⁆ * q⁻¹ * ⁅q, (b' : G)⁆ := by
      simp only [commutatorElement_def]; group
    show ⁅q * w, (b' : G)⁆ ∈ iHull15 V₀ U H
    rw [key]
    exact (iHull15 V₀ U H).mul_mem
      ((Subgroup.mem_normalizer_iff.1 (hHI hqH) _).1 (hV w hw)) (hQ q hq)

end Certified

end Cfg1511

section Certified


theorem w15Eleven4Bar_holds : W15Eleven4Bar G := by
  intro M V₀ V U S H P Q₀ p c X v hX hXc Y B hYX hYp hYc hBT hBe hBY
  exact c.exists_relIndex_le_two_commutator_mem hX hXc hYX hYp hYc hBT hBe hBY

end Certified

end CFSG.LocalAnalysis.WeakClosure81
