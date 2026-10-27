module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecNS

public section

namespace CFSG.Quasithin.H13.P31Sec

variable {S : Type} [Group S]

theorem IsSubnormalSection.of_normal {Q : Type} [Group Q] (A : Subgroup Q) [hA : A.Normal]
    {W : Type} [Group W] (h : IsSubnormalSection W ↥A) : IsSubnormalSection W Q := by
  obtain ⟨M, N, hN, hNM, hNs, hMs, ⟨e⟩⟩ := h
  set M' : Subgroup Q := M.map A.subtype with hM'
  set N' : Subgroup Q := N.map A.subtype with hN'
  have hNM' : N' ≤ M' := Subgroup.map_mono hNM
  let ιM : ↥M →* ↥M' := A.subtype.subgroupMap M
  have hιM : Function.Surjective ιM := A.subtype.subgroupMap_surjective M
  have hιMi : Function.Injective ιM := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun x : ↥M' => ((x : Q))) hab))
  have hNeq : N'.subgroupOf M' = (N.subgroupOf M).map ιM := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn, hny⟩ := Subgroup.mem_subgroupOf.1 hy
      refine ⟨⟨n, hNM hn⟩, Subgroup.mem_subgroupOf.2 hn, ?_⟩
      exact Subtype.ext hny
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.2 ⟨(x : ↥A), Subgroup.mem_subgroupOf.1 hx, rfl⟩
  haveI : (N'.subgroupOf M').Normal := by
    rw [hNeq]
    exact hN.map ιM hιM
  have hsub : ∀ X : Subgroup ↥A, X.IsSubnormal → (X.map A.subtype).IsSubnormal := by
    intro X hX
    have hle : X.map A.subtype ≤ A := Subgroup.map_subtype_le X
    have h1 : ((X.map A.subtype).subgroupOf A) = X :=
      Subgroup.comap_map_eq_self_of_injective A.subtype_injective X
    have h2 : ((X.map A.subtype).subgroupOf A).IsSubnormal := by
      rw [h1]
      exact hX
    exact Subgroup.IsSubnormal.trans hle h2 (Subgroup.Normal.isSubnormal hA)
  refine ⟨M', N', inferInstance, hNM', hsub N hNs, hsub M hMs, ?_⟩
  let eM : ↥M ≃* ↥M' := MulEquiv.ofBijective ιM ⟨hιMi, hιM⟩
  have hmap : Subgroup.map (↑eM) (N.subgroupOf M) = N'.subgroupOf M' := hNeq.symm
  exact ⟨((QuotientGroup.congr (N.subgroupOf M) (N'.subgroupOf M') eM hmap).symm).trans e⟩

theorem AllNS.of_normal {Q : Type} [Group Q] (A : Subgroup Q) [A.Normal] (h : AllNS S Q) :
    AllNS S ↥A :=
  fun W _ hs hnab hsec => h W hs hnab (IsSubnormalSection.of_normal A hsec)

theorem AllNS.nonempty_equiv {W : Type} [Group W] (h : AllNS S W) (hW : IsSimpleGroup W)
    (hnab : ∃ a b : W, a * b ≠ b * a) : Nonempty (W ≃* S) := by
  have hbot : (⊥ : Subgroup W).subgroupOf (⊤ : Subgroup W) = ⊥ := by simp
  haveI : ((⊥ : Subgroup W).subgroupOf (⊤ : Subgroup W)).Normal := by
    rw [hbot]
    infer_instance
  refine h W hW hnab ⟨⊤, ⊥, inferInstance, bot_le, Subgroup.Normal.isSubnormal inferInstance,
    Subgroup.IsSubnormal.top, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hbot).trans
    ((QuotientGroup.quotientBot).trans Subgroup.topEquiv)

end CFSG.Quasithin.H13.P31Sec
