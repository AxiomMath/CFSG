module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110Complement
public import CFSG.RankThree.GF2n.Stroth80.Sec1110Stable

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix Pointwise

variable {G : Type} [Group G]

theorem sectionAct_on_complement {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q R X₄ X₂ W Z : Subgroup G}
    {φ : R →* GL ι K} {act : GL ι K → Matrix ι ι K}
    (hact : SectionAct K R X₄ X₂ φ act)
    (hX₂Q : X₂ ≤ Q) (hX₄Q : X₄ ≤ Q) (hX₂X₄ : X₂ ≤ X₄) (hWX₄ : W ≤ X₄)
    (hZW : Z ≤ W) (hinf : W ⊓ X₂ = Z) (hsup : W ⊔ X₂ = Q)
    (hWinv : ∀ r ∈ R, conjSubgroup r W = W) :
    SectionAct K R W Z φ act := by
  obtain ⟨-, hN, ψ, hψ⟩ := hact
  haveI := hN
  have hZnorm : (Z.subgroupOf W).Normal := by
    have h := Subgroup.inf_subgroupOf_inf_normal_of_right (A := W) (B' := X₂) (B := X₄)
    rwa [inf_of_le_left hWX₄, hinf] at h
  letI : (Z.subgroupOf W).Normal := hZnorm
  let f : ↥W →* ↥X₄ := Subgroup.inclusion hWX₄
  have hf : Z.subgroupOf W ≤ (X₂.subgroupOf X₄).comap f := by
    intro z hz
    rw [Subgroup.mem_comap]
    have hzZ : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz
    rw [← hinf] at hzZ
    show ((f z : ↥X₄) : G) ∈ X₂
    rw [Subgroup.coe_inclusion]
    exact hzZ.2
  let g : ↥W ⧸ Z.subgroupOf W →* ↥X₄ ⧸ X₂.subgroupOf X₄ :=
    QuotientGroup.map (Z.subgroupOf W) (X₂.subgroupOf X₄) f hf
  have hg_mk : ∀ w : ↥W, g (QuotientGroup.mk w) =
      QuotientGroup.mk (⟨(w : G), hWX₄ w.2⟩ : ↥X₄) := by
    intro w
    rw [show g (QuotientGroup.mk w) =
        QuotientGroup.map (Z.subgroupOf W) (X₂.subgroupOf X₄) f hf
          (QuotientGroup.mk w) from rfl]
    rw [QuotientGroup.map_mk]
    rfl
  have hker : g.ker = ⊥ := by
    rw [show g = QuotientGroup.map (Z.subgroupOf W) (X₂.subgroupOf X₄) f hf from rfl,
      QuotientGroup.ker_map]
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    have hwX₂ : (w : G) ∈ X₂ := by
      have h1 : f w ∈ X₂.subgroupOf X₄ := Subgroup.mem_comap.mp hw
      have h2 : ((f w : ↥X₄) : G) ∈ X₂ := Subgroup.mem_subgroupOf.mp h1
      rwa [Subgroup.coe_inclusion] at h2
    have hwZ : w ∈ Z.subgroupOf W := by
      rw [Subgroup.mem_subgroupOf]
      exact hinf ▸ Subgroup.mem_inf.mpr ⟨w.2, hwX₂⟩
    simpa using (QuotientGroup.eq_one_iff (N := Z.subgroupOf W) w).mpr hwZ
  have hinj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff, hker]
  have hsurj : Function.Surjective g := by
    intro c
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    have hxQ : (x : G) ∈ Q := hX₄Q x.2
    rw [← hsup] at hxQ
    have hX₄_norm : X₄ ≤ Subgroup.normalizer (X₂ : Set G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf hX₂X₄
    have hWnorm : W ≤ Subgroup.normalizer (X₂ : Set G) := hWX₄.trans hX₄_norm
    have hprod : ((W ⊔ X₂ : Subgroup G) : Set G) = (W : Set G) * (X₂ : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right W X₂ hWnorm
    have hxQ' : (x : G) ∈ ((W ⊔ X₂ : Subgroup G) : Set G) := hxQ
    rw [hprod, Set.mem_mul] at hxQ'
    obtain ⟨y, hyW, z, hzX₂, hyz⟩ := hxQ'
    have hzX₄ : z ∈ X₄ := by
      have hz : z = y⁻¹ * (x : G) := by rw [← hyz]; group
      rw [hz]
      exact X₄.mul_mem (X₄.inv_mem (hWX₄ hyW)) x.2
    refine ⟨QuotientGroup.mk (⟨y, hyW⟩ : ↥W), ?_⟩
    rw [hg_mk]
    have hzq : (QuotientGroup.mk (⟨z, hzX₄⟩ : ↥X₄) :
        ↥X₄ ⧸ X₂.subgroupOf X₄) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hzX₂)
    rw [show (QuotientGroup.mk (⟨y, hWX₄ hyW⟩ : ↥X₄)) =
        QuotientGroup.mk (⟨y * z, X₄.mul_mem (hWX₄ hyW) hzX₄⟩ : ↥X₄) by
      rw [show (⟨y * z, X₄.mul_mem (hWX₄ hyW) hzX₄⟩ : ↥X₄) =
          (⟨y, hWX₄ hyW⟩ : ↥X₄) * ⟨z, hzX₄⟩ from rfl,
        QuotientGroup.mk_mul, hzq, mul_one]]
    congr 1
    exact Subtype.ext hyz
  let e : ↥W ⧸ Z.subgroupOf W ≃* ↥X₄ ⧸ X₂.subgroupOf X₄ :=
    MulEquiv.ofBijective g ⟨hinj, hsurj⟩
  have he_mk : ∀ w : ↥W, e (QuotientGroup.mk w) =
      QuotientGroup.mk (⟨(w : G), hWX₄ w.2⟩ : ↥X₄) := by
    intro w
    rw [show e (QuotientGroup.mk w) = g (QuotientGroup.mk w) from rfl]
    exact hg_mk w
  refine ⟨?_, hZnorm, e.trans ψ, ?_⟩
  · intro r hr
    exact conjSubgroup_eq_self_iff.mp (hWinv r hr)
  · intro s v w hw
    have hψw := hψ s ⟨(v : G), hWX₄ v.2⟩ ⟨(w : G), hWX₄ w.2⟩ (by simpa using hw)
    simpa [MulEquiv.trans_apply, he_mk] using hψw

section Final

variable [Finite G]
variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
variable {n : ℕ}

theorem caseVICore_of_chain_final
    (hc : Ctx M Q Z B) (hw : Width Q Z n) (hn : 3 ≤ n)
    (hD : GlobalModelData M Q Z γ M₀)
    (hK : Nat.card K = Nat.card Z)
    {X₁ X₂ X₃ X₄ : Subgroup G}
    (hX₁ : X₁ = Z) (h₁₂ : X₁ ≤ X₂) (h₂₃ : X₂ ≤ X₃) (h₃₄ : X₃ ≤ X₄) (h₄Q : X₄ ≤ Q)
    (hX₂ : X₂ = Z ⊔ ⁅X₃, XbarPre M Q Z B⁆) (hX₃ : X₃ = X₂)
    (hX₄ : X₄ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆)
    (nat2 : NaturalRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₂ X₁ (Q))
    (nat4 : NaturalDualRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₄ X₃ (Q))
    (hstable : PiImageStable M₀ X₂) :
    CaseVICore M Q Z (XbarPre M Q Z B) n := by
  have hZ₂ : Z ≤ X₂ := by rw [← hX₁]; exact h₁₂
  have hX₂Q : X₂ ≤ Q := fun x hx => h₄Q (h₃₄ (h₂₃ hx))
  obtain ⟨x, hxM, hWin, hWsup⟩ :=
    exists_conj_complement (M₀ := M₀) hc hw hn hD hZ₂ hX₂Q hX₁ nat2
  let W : Subgroup G := conjSubgroup x X₂
  have hnorm₂ : XbarPre M Q Z B ≤ Subgroup.normalizer (X₂ : Set G) := by
    have nat2keep : NaturalRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₂ X₁ (Q) :=
      nat2
    obtain ⟨-, -, -, hnorm, -, -, -⟩ := nat2keep
    exact hnorm
  have hZW : Z ≤ W := by
    calc Z = conjSubgroup x Z := (hc.conj_Z_eq hxM).symm
      _ ≤ conjSubgroup x X₂ := Subgroup.map_mono hZ₂
      _ = W := rfl
  have hWQ : W ≤ Q := by
    calc W = conjSubgroup x X₂ := rfl
      _ ≤ conjSubgroup x Q := Subgroup.map_mono hX₂Q
      _ = Q := hc.conj_Q_eq hxM
  have hX₄_normal : ∀ m ∈ M, conjSubgroup m X₄ = X₄ := by
    intro m hm
    have hZ : conjSubgroup m Z = Z := hc.conj_Z_eq hm
    have hQ : conjSubgroup m Q = Q := hc.conj_Q_eq hm
    have hX : conjSubgroup m (XbarPre M Q Z B) = XbarPre M Q Z B :=
      XbarPre_normal hc hm
    have hcomm : conjSubgroup m ⁅Q, XbarPre M Q Z B⁆ = ⁅Q, XbarPre M Q Z B⁆ := by
      have hmap : conjSubgroup m ⁅Q, XbarPre M Q Z B⁆ =
          ⁅conjSubgroup m Q, conjSubgroup m (XbarPre M Q Z B)⁆ :=
        Subgroup.map_commutator (H₁ := Q) (H₂ := XbarPre M Q Z B)
          (f := (MulAut.conj m).toMonoidHom)
      rw [hmap, hQ, hX]
    have hsupmap : conjSubgroup m (Z ⊔ ⁅Q, XbarPre M Q Z B⁆) =
        conjSubgroup m Z ⊔ conjSubgroup m ⁅Q, XbarPre M Q Z B⁆ :=
      Subgroup.map_sup Z ⁅Q, XbarPre M Q Z B⁆ (MulAut.conj m).toMonoidHom
    calc conjSubgroup m X₄
        = conjSubgroup m (Z ⊔ ⁅Q, XbarPre M Q Z B⁆) := by rw [hX₄]
      _ = conjSubgroup m Z ⊔ conjSubgroup m ⁅Q, XbarPre M Q Z B⁆ := hsupmap
      _ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆ := by rw [hZ, hcomm]
      _ = X₄ := hX₄.symm
  have hZ_le_X₄ : Z ≤ X₄ := by
    have h : X₁ ≤ X₄ := h₁₂.trans (h₂₃.trans h₃₄)
    rwa [hX₁] at h
  have hX₂_le_X₄ : X₂ ≤ X₄ := by
    rw [hX₂, hX₃]
    refine sup_le hZ_le_X₄ ?_
    calc ⁅X₂, XbarPre M Q Z B⁆ ≤ ⁅Q, XbarPre M Q Z B⁆ :=
          Subgroup.commutator_mono hX₂Q le_rfl
      _ ≤ X₄ := by rw [hX₄]; exact le_sup_right
  have hW_le_X₄ : W ≤ X₄ := by
    calc W = conjSubgroup x X₂ := rfl
      _ ≤ conjSubgroup x X₄ := Subgroup.map_mono hX₂_le_X₄
      _ = X₄ := hX₄_normal x hxM
  have hWinv : ∀ r ∈ XbarPre M Q Z B, conjSubgroup r W = W := by
    intro r hr
    have hxrx : x⁻¹ * r * x ∈ XbarPre M Q Z B := by
      have hm : r ∈ conjSubgroup x (XbarPre M Q Z B) := by
        rw [XbarPre_normal hc hxM]
        exact hr
      exact mem_conjSubgroup.mp hm
    have hnorm : conjSubgroup (x⁻¹ * r * x) X₂ = X₂ :=
      conjSubgroup_eq_self_iff.mpr (hnorm₂ hxrx)
    calc conjSubgroup r W
        = conjSubgroup r (conjSubgroup x X₂) := rfl
      _ = conjSubgroup (r * x) X₂ := conjSubgroup_conjSubgroup r x X₂
      _ = conjSubgroup x (conjSubgroup (x⁻¹ * r * x) X₂) := by
          rw [conjSubgroup_conjSubgroup x (x⁻¹ * r * x) X₂]
          congr 1
          group
      _ = conjSubgroup x X₂ := by rw [hnorm]
      _ = W := rfl
  have hact₄ : SectionAct K (XbarPre M Q Z B) X₄ X₂ (Classical.choose nat2)
      (fun g => (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ) :=
    sectionAct_dual_on_quotient (M₀ := M₀) hn hX₁ hX₂ hX₃ hX₄ h₁₂ h₂₃ h₃₄ h₄Q hc hD
      nat2 nat4 hstable
  have hactW : SectionAct K (XbarPre M Q Z B) W Z (Classical.choose nat2)
      (fun g => (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ) :=
    sectionAct_on_complement (Q := Q) (R := XbarPre M Q Z B) (X₄ := X₄) (X₂ := X₂)
      (W := W) (Z := Z) hact₄ hX₂Q h₄Q hX₂_le_X₄ hW_le_X₄ hZW
      (by rw [inf_comm]; exact hWin) (by rw [sup_comm]; exact hWsup) hWinv
  exact caseVICore_of_chain_with_complement (n := n) hK hX₁ h₁₂ h₂₃ h₃₄ h₄Q hZW hWQ
    (by rw [inf_comm]; exact hWin) (by rw [sup_comm]; exact hWsup) nat2 hactW
    ⟨x, hxM, rfl⟩

theorem caseVICore_of_chain_final_unconditional
    (hc : Ctx M Q Z B) (hw : Width Q Z n) (hn : 3 ≤ n)
    (hD : GlobalModelData M Q Z γ M₀)
    (hK : Nat.card K = Nat.card Z)
    {X₁ X₂ X₃ X₄ : Subgroup G}
    (hX₁ : X₁ = Z) (h₁₂ : X₁ ≤ X₂) (h₂₃ : X₂ ≤ X₃) (h₃₄ : X₃ ≤ X₄) (h₄Q : X₄ ≤ Q)
    (hX₂ : X₂ = Z ⊔ ⁅X₃, XbarPre M Q Z B⁆) (hX₃ : X₃ = X₂)
    (hX₄ : X₄ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆)
    (nat2 : NaturalRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₂ X₁ (Q))
    (nat4 : NaturalDualRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₄ X₃ (Q)) :
    CaseVICore M Q Z (XbarPre M Q Z B) n :=
  caseVICore_of_chain_final hc hw hn hD hK hX₁ h₁₂ h₂₃ h₃₄ h₄Q hX₂ hX₃ hX₄ nat2 nat4
    (piImageStable_of_naturalRep hn hX₁ hX₂ hX₃ hX₄ h₁₂ h₂₃ h₃₄ h₄Q hc hD nat2 nat4)

end Final


end CFSG.RankThree.GF2n.Stroth80
