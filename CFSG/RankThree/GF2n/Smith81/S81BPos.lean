module

public import CFSG.RankThree.GF2n.Smith81.S81BBridge
public import CFSG.RankThree.GF2n.Smith81.ETables

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {V : Type} [AddCommGroup V] [Module K V] {ψ : M₀.E ≃ₗ[K] V}
  {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)} {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V}
  {U₀ : Subgroup (V ≃ₗ[K] V)}

@[expose] def EGeom.EUniData.IsPt (_d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) (X : Subgroup G)
    (g : V ≃ₗ[K] V) : Prop :=
  g ∈ Γ ∧ (fun a : G => ψ (M₀.π a)) '' (X : Set G) = (Submodule.span K {g p₀} : Set V) ∧
    ∀ u ∈ conjSub g U₀, ∃ t : Lgen M (LB M Q B), (t : G) ∈ QB X ∧ φ t = u

theorem EGeom.EUniData.exists_isPt (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {X : Subgroup G}
    (hX : Ctx M Q Z X) : ∃ g, d.IsPt X g := by
  obtain ⟨g, hg, h1, h2⟩ := d.point X hX.conj hX.le hX.ne
  exact ⟨g, hg, h1, h2⟩

theorem eq_of_psi_image_eq (ψ : M₀.E ≃ₗ[K] V) {X Y : Subgroup G} (hXQ : X ≤ Q) (hYQ : Y ≤ Q)
    (hXZ : Z ≤ X) (hYZ : Z ≤ Y)
    (h : (fun a : G => ψ (M₀.π a)) '' (X : Set G) = (fun a : G => ψ (M₀.π a)) '' (Y : Set G)) :
    X = Y := by
  have key : ∀ {X Y : Subgroup G}, X ≤ Q → Y ≤ Q → Z ≤ Y →
      (fun a : G => ψ (M₀.π a)) '' (X : Set G) = (fun a : G => ψ (M₀.π a)) '' (Y : Set G) →
      X ≤ Y := by
    intro X Y hXQ hYQ hYZ h x hx
    have hmem : ψ (M₀.π x) ∈ (fun a : G => ψ (M₀.π a)) '' (X : Set G) := ⟨x, hx, rfl⟩
    rw [h] at hmem
    obtain ⟨y, hy, hyeq⟩ := hmem
    have hyeq' : ψ (M₀.π y) = ψ (M₀.π x) := hyeq
    have hpi : M₀.π y = M₀.π x := ψ.injective hyeq'
    have hxQ : x ∈ Q := hXQ hx
    have hyQ : y ∈ Q := hYQ hy
    have h0 : M₀.π (x * y⁻¹) = 0 := by
      rw [M₀.π_mul x hxQ y⁻¹ (Q.inv_mem hyQ), quadModel_pi_inv M₀ hyQ, hpi]
      simp
    have hmemZ : x * y⁻¹ ∈ Z :=
      (M₀.π_ker (x * y⁻¹) (Q.mul_mem hxQ (Q.inv_mem hyQ))).mp h0
    have hxy : x * y⁻¹ * y ∈ Y := Y.mul_mem (hYZ hmemZ) hy
    simpa using hxy
  exact le_antisymm (key hXQ hYQ hYZ h) (key hYQ hXQ hXZ h.symm)

theorem psi_image_sup_Z (ψ : M₀.E ≃ₗ[K] V) {X : Subgroup G} (hXQ : X ≤ Q) (hZQ : Z ≤ Q) :
    (fun a : G => ψ (M₀.π a)) '' ((X ⊔ Z : Subgroup G) : Set G) =
      (fun a : G => ψ (M₀.π a)) '' (X : Set G) := by
  obtain ⟨T, hT⟩ : ∃ T : Subgroup G, ∀ x : G,
      x ∈ T ↔ (x ∈ Q ∧ ∃ y ∈ X, ψ (M₀.π x) = ψ (M₀.π y)) :=
    ⟨{ carrier := {x : G | x ∈ Q ∧ ∃ y ∈ X, ψ (M₀.π x) = ψ (M₀.π y)}
       mul_mem' := by
         rintro a b ⟨ha, y, hy, hay⟩ ⟨hb, z, hz, hbz⟩
         refine ⟨Q.mul_mem ha hb, y * z, X.mul_mem hy hz, ?_⟩
         rw [M₀.π_mul a ha b hb, map_add, hay, hbz, M₀.π_mul y (hXQ hy) z (hXQ hz), map_add]
       one_mem' := ⟨Q.one_mem, 1, X.one_mem, rfl⟩
       inv_mem' := by
         rintro a ⟨ha, y, hy, hay⟩
         refine ⟨Q.inv_mem ha, y⁻¹, X.inv_mem hy, ?_⟩
         rw [quadModel_pi_inv M₀ ha, quadModel_pi_inv M₀ (hXQ hy), map_neg, map_neg, hay] },
     fun x => Iff.rfl⟩
  have hXT : X ≤ T := fun x hx => (hT x).mpr ⟨hXQ hx, x, hx, rfl⟩
  have hZT : Z ≤ T := fun z hz => (hT z).mpr
    ⟨hZQ hz, 1, X.one_mem, by rw [(M₀.π_ker z (hZQ hz)).mpr hz, quadModel_pi_one M₀]⟩
  have hsup : X ⊔ Z ≤ T := sup_le hXT hZT
  refine Set.Subset.antisymm ?_ ?_
  · rintro v ⟨a, ha, rfl⟩
    obtain ⟨_, y, hy, hay⟩ := (hT a).mp (hsup (SetLike.mem_coe.mp ha))
    exact ⟨y, hy, hay.symm⟩
  · exact Set.image_mono (SetLike.coe_subset_coe.mpr le_sup_left)

theorem EGeom.EUniData.epos_eq_iff (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {B' C' : Subgroup G}
    (hB' : Ctx M Q Z B') (hC' : Ctx M Q Z C') {gB gC : V ≃ₗ[K] V} (hgB : d.IsPt B' gB)
    (hgC : d.IsPt C' gC) :
    EPosEq Z B' C' ↔ Submodule.span K {gC p₀} = Submodule.span K {gB p₀} := by
  have hZQ : Z ≤ Q := hB'.hyp.Z_normal.1
  have hCQ : C' ⊔ Z ≤ Q := sup_le hC'.le hZQ
  have hBQ : B' ⊔ Z ≤ Q := sup_le hB'.le hZQ
  have himC : (fun a : G => ψ (M₀.π a)) '' ((C' ⊔ Z : Subgroup G) : Set G) =
      (Submodule.span K {gC p₀} : Set V) := by
    rw [psi_image_sup_Z ψ hC'.le hZQ]
    exact hgC.2.1
  have himB : (fun a : G => ψ (M₀.π a)) '' ((B' ⊔ Z : Subgroup G) : Set G) =
      (Submodule.span K {gB p₀} : Set V) := by
    rw [psi_image_sup_Z ψ hB'.le hZQ]
    exact hgB.2.1
  constructor
  · intro h
    have h0 : C' ⊔ Z = B' ⊔ Z := h
    have h' : (fun a : G => ψ (M₀.π a)) '' ((C' ⊔ Z : Subgroup G) : Set G) =
        (fun a : G => ψ (M₀.π a)) '' ((B' ⊔ Z : Subgroup G) : Set G) := by
      rw [h0]
    rw [himC, himB] at h'
    exact SetLike.coe_injective h'
  · intro h
    have hset : (Submodule.span K {gC p₀} : Set V) = (Submodule.span K {gB p₀} : Set V) := by
      rw [h]
    have h' : (fun a : G => ψ (M₀.π a)) '' ((C' ⊔ Z : Subgroup G) : Set G) =
        (fun a : G => ψ (M₀.π a)) '' ((B' ⊔ Z : Subgroup G) : Set G) := by
      rw [himC, himB]
      exact hset
    exact eq_of_psi_image_eq ψ hCQ hBQ le_sup_right le_sup_right h'

theorem EGeom.EUniData.epos_Q_iff (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {B' C' : Subgroup G}
    (hB' : Ctx M Q Z B') (hC' : Ctx M Q Z C') {gB gC : V ≃ₗ[K] V} (hgB : d.IsPt B' gB)
    (hgC : d.IsPt C' gC) {n : ℕ} (hcard : Nat.card ↥(Q ⊓ QB B') = Nat.card Z ^ (n + 1))
    (hW : Nat.card (Wsp (Submodule.span K {p₀}) U₀) ≤ Nat.card K ^ n)
    (hK : Nat.card K = Nat.card Z) :
    EPosQ Z B' C' ↔ Submodule.span K {gC p₀} ≠ Submodule.span K {gB p₀} ∧
      gC p₀ ∈ Wsp (Submodule.span K {gB p₀}) (conjSub gB U₀) := by
  have hgCmem : gC p₀ ∈ (fun a : G => ψ (M₀.π a)) '' (C' : Set G) := by
    rw [hgC.2.1]
    exact Submodule.subset_span (Set.mem_singleton _)
  refine ⟨fun hQpos => ?_, fun hWpos => ?_⟩
  · obtain ⟨hne, hQ⟩ := hQpos
    refine ⟨fun h => hne ((d.epos_eq_iff hB' hC' hgB hgC).mpr h), ?_⟩
    obtain ⟨c, hcC, hc⟩ := hgCmem
    have hc' : ψ (M₀.π c) = gC p₀ := hc
    have hcQB : c ∈ Q ⊓ QB B' := Subgroup.mem_inf.mpr ⟨hC'.le hcC, hQ hcC⟩
    have hW' := d.psi_mem_Wsp (g := gB) hB' hgB.2.1 hgB.2.2 hcQB
    rw [hc'] at hW'
    exact hW'
  · obtain ⟨hne, hWgC⟩ := hWpos
    show C' ⊔ Z ≠ B' ⊔ Z ∧ C' ≤ QB B'
    refine ⟨fun h => hne ((d.epos_eq_iff hB' hC' hgB hgC).mp h), ?_⟩
    have hsub : Submodule.span K {gC p₀} ≤ Wsp (Submodule.span K {gB p₀}) (conjSub gB U₀) :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hWgC)
    intro c hcC'
    have hcimg : ψ (M₀.π c) ∈ (Submodule.span K {gC p₀} : Set V) := by
      rw [← hgC.2.1]
      exact ⟨c, hcC', rfl⟩
    obtain ⟨y, hy, hyc⟩ := d.exists_mem_inf_of_mem_Wsp (g := gB) hB' hgB.2.1 hgB.2.2 hcard hW hK
      (ψ (M₀.π c)) (hsub hcimg)
    have hπ : M₀.π y = M₀.π c := ψ.injective hyc
    obtain ⟨hyQ, hyQB⟩ := Subgroup.mem_inf.mp hy
    have hcQ : c ∈ Q := hC'.le hcC'
    have hpi : M₀.π (c * y⁻¹) = 0 := by
      rw [M₀.π_mul c hcQ y⁻¹ (Q.inv_mem hyQ), quadModel_pi_inv M₀ hyQ, hπ]
      abel
    have hzZ : c * y⁻¹ ∈ Z := (M₀.π_ker (c * y⁻¹) (Q.mul_mem hcQ (Q.inv_mem hyQ))).mp hpi
    have h := (QB B').mul_mem (hB'.Z_le_QB.1 hzZ) hyQB
    simpa using h

theorem Ctx.le_normalizer_iff_comm {B' C' : Subgroup G} (hB' : Ctx M Q Z B') (hC' : Ctx M Q Z C') :
    C' ≤ Subgroup.normalizer (B' : Set G) ↔ ∀ c ∈ C', ∀ b ∈ B', c * b = b * c := by
  constructor
  · intro hle c hc b hb
    have hcb : c * b * c⁻¹ ∈ B' := (Subgroup.mem_normalizer_iff.mp (hle hc) b).mp hb
    have hZmem : ⁅c, b⁆ ∈ Z := hB'.hyp.toHyp79.comm_mem_V (hC'.le hc) (hB'.le hb)
    obtain ⟨g, hg⟩ := hB'.conj
    have hgZ : conjSubgroup g Z ≠ Z := by
      rw [← hg]
      exact hB'.ne
    have hZB : Z ⊓ B' = ⊥ := by
      rw [hg]
      exact CFSG.RankThree.GF2n.inf_conjSubgroup_eq_bot_of_isTI hB'.hyp.ti hgZ
    have hBmem : ⁅c, b⁆ ∈ B' := by
      rw [commutatorElement_def]
      exact B'.mul_mem hcb (B'.inv_mem hb)
    have hbot : ⁅c, b⁆ ∈ Z ⊓ B' := Subgroup.mem_inf.mpr ⟨hZmem, hBmem⟩
    rw [hZB, Subgroup.mem_bot] at hbot
    exact commutatorElement_eq_one_iff_mul_comm.mp hbot
  · intro h
    exact CFSG.RankThree.GF2n.le_normalizer_of_comm h

theorem EGeom.EUniData.comm_iff_beta (hg : GlobalModelData M Q Z γ M₀)
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {B' C' : Subgroup G} (hB' : Ctx M Q Z B')
    (hC' : Ctx M Q Z C') {gB gC : V ≃ₗ[K] V} (hgB : d.IsPt B' gB) (hgC : d.IsPt C' gC)
    {β : V →ₗ[K] V →ₗ[K] K} {lam : K} (hlam : lam ≠ 0)
    (hform : ∀ e f : M₀.E, M₀.B e f = lam * β (ψ e) (ψ f)) :
    (∀ c ∈ C', ∀ b ∈ B', c * b = b * c) ↔ β (gC p₀) (gB p₀) = 0 := by
  obtain ⟨-, hCimg, -⟩ := hgC
  obtain ⟨-, hBimg, -⟩ := hgB
  have key : ∀ c ∈ C', ∀ b ∈ B', c * b = b * c ↔ β (ψ (M₀.π c)) (ψ (M₀.π b)) = 0 := by
    intro c hcC b hbB
    rw [Tim79.QuadModel.comm_iff_B M₀ hg.reg (hC'.le hcC) (hB'.le hbB), hform, mul_eq_zero,
      or_iff_right hlam]
  constructor
  · intro h
    have hcI : gC p₀ ∈ (fun a : G => ψ (M₀.π a)) '' (C' : Set G) := by
      rw [hCimg]
      exact SetLike.mem_coe.mpr (Submodule.mem_span_singleton_self _)
    have hbI : gB p₀ ∈ (fun a : G => ψ (M₀.π a)) '' (B' : Set G) := by
      rw [hBimg]
      exact SetLike.mem_coe.mpr (Submodule.mem_span_singleton_self _)
    obtain ⟨c, hcC, hc⟩ := hcI
    obtain ⟨b, hbB, hb⟩ := hbI
    have hc' : ψ (M₀.π c) = gC p₀ := hc
    have hb' : ψ (M₀.π b) = gB p₀ := hb
    have h0 := (key c hcC b hbB).mp (h c hcC b hbB)
    rw [hc', hb'] at h0
    exact h0
  · intro h c hcC b hbB
    apply (key c hcC b hbB).mpr
    have hcS : ψ (M₀.π c) ∈ Submodule.span K {gC p₀} := by
      have h1 : (fun a : G => ψ (M₀.π a)) c ∈ (fun a : G => ψ (M₀.π a)) '' (C' : Set G) :=
        Set.mem_image_of_mem (fun a : G => ψ (M₀.π a)) (SetLike.mem_coe.mpr hcC)
      rw [hCimg] at h1
      exact SetLike.mem_coe.mp h1
    have hbS : ψ (M₀.π b) ∈ Submodule.span K {gB p₀} := by
      have h1 : (fun a : G => ψ (M₀.π a)) b ∈ (fun a : G => ψ (M₀.π a)) '' (B' : Set G) :=
        Set.mem_image_of_mem (fun a : G => ψ (M₀.π a)) (SetLike.mem_coe.mpr hbB)
      rw [hBimg] at h1
      exact SetLike.mem_coe.mp h1
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hcS
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hbS
    rw [← hs, ← ht]
    simp [map_smul, LinearMap.smul_apply, h]

end CFSG.RankThree.GF2n.Smith81
