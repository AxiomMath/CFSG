module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixGamma
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigO
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigS7
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigS6
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispUC
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMLin

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnitSix_orthY_symplectic
    (hK : Nat.card K = 4)
    {L Bs : Subgroup G} {Q : Type} [Group Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q}
    {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    (hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)
    (hBsE : IsElemAbelian 3 Bs)
    (hSC : ∀ h ∈ Subgroup.centralizer (Bs : Set G), h ^ 3 = 1 → h ∈ Bs)
    (hcard : Nat.card Bs = 3 ^ 6) {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    {x : G} (hxBs : x ∈ Bs) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1)
    {a c : Fin 6} (hac : a ≠ c) {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {b' : ↥Bs}
    (hb' : βL (Additive.ofMul b') = Pi.single c 1) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁N : J₁ ≤ N) (hJ₂N : J₁.map (MulAut.conj g).toMonoidHom ≤ N)
    (hBsN : Bs ≤ Subgroup.normalizer (N : Set G)) {𝒦 : Finset (Subgroup G)}
    (hjoin : ∀ w ∈ dEven 6, ∃ a ∈ ggAutomizerJoin L Bs 𝒦,
      ∀ s : ↥Bs, βL (Additive.ofMul (a s)) = w (βL (Additive.ofMul s)))
    (hlab : GGHasLabel ⟨.C, 5, 1⟩ (↥N ⧸ Subgroup.center ↥N)) :
    ∃ Y : Subgroup G, J₁ ≤ Y ∧ J₁.map (MulAut.conj g).toMonoidHom ≤ Y ∧
      ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = 5 ∧
        Subgroup.center ↥Y = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperfN : Group.IsPerfect ↥N := Group.isPerfect_def.mpr (qtwoDB36_perfect hN)
  obtain ⟨hZ, ⟨eN⟩⟩ := qtwoDB44_model (N := ↥N) (d := 5) (by norm_num) hlab
  obtain ⟨τ, hτker, hconj, hscτ, hWτ, hJ1c, hJ2c⟩ := ggQTwoDUnitSix_torus_N hK hD hψk hε hBsE hSC
    hcard hω hind hpermβ hxBs hxL hxcoord hac hJ₁L hJ₁Z hJ₁ hα hgN hg hb' hN hJ₁N hJ₂N hBsN hjoin
    hZ
  have hJ₁p : J₁ ≤ ⁅J₁, J₁⁆ := Subgroup.commutator_eq_self.ge
  have hJ₂p : J₁.map (MulAut.conj g).toMonoidHom ≤
      ⁅J₁.map (MulAut.conj g).toMonoidHom, J₁.map (MulAut.conj g).toMonoidHom⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hJ₁p
  refine qtwoDB44_case_symplectic_of (m := 6) (by norm_num) hBsE hSC hBsN eN τ hτker hconj hscτ
    hWτ hJ₁N hJ₁p (fun i _ => one_ne_zero) hJ1c hJ₂N hJ₂p (fun i _ => ?_) hJ2c
    (s₀ := ⟨x, hxBs⟩) ⟨a, hac, by rw [hxcoord]; exact one_ne_zero⟩
  rw [dSign_apply_vec]
  split_ifs
  · exact neg_ne_zero.mpr one_ne_zero
  · exact one_ne_zero

theorem ggQTwoDUnitSix_orthY_twD6
    (hRig : GGLabelRigidInput) (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type} [Group Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    (hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)
    (hBsE : IsElemAbelian 3 Bs)
    (hSC : ∀ h ∈ Subgroup.centralizer (Bs : Set G), h ^ 3 = 1 → h ∈ Bs)
    (hcard : Nat.card Bs = 3 ^ 6) {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    {x : G} (hxBs : x ∈ Bs) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1)
    {a c : Fin 6} (hac : a ≠ c) {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {b' : ↥Bs}
    (hb' : βL (Additive.ofMul b') = Pi.single c 1) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁N : J₁ ≤ N) (hJ₂N : J₁.map (MulAut.conj g).toMonoidHom ≤ N)
    (hinner : GGInnerDiagOn Bs N) {𝒦 : Finset (Subgroup G)}
    (hjoin : ∀ w ∈ dEven 6, ∃ a ∈ ggAutomizerJoin L Bs 𝒦,
      ∀ s : ↥Bs, βL (Additive.ofMul (a s)) = w (βL (Additive.ofMul s)))
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N)) (hlab6 : lab = ⟨.twD, 6, 1⟩) :
    ∃ Y : Subgroup G, J₁ ≤ Y ∧ J₁.map (MulAut.conj g).toMonoidHom ≤ Y ∧
      ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = 5 ∧
        Subgroup.center ↥Y = ⊥ := by
  have hBsN : Bs ≤ Subgroup.normalizer (N : Set G) := hinner.le_normalizer
  obtain ⟨Θ, -, hΘact⟩ := ggQTwoDUnitSix_weyl_embed hK hD hψk hε hBsE hSC hcard hω hind hpermβ
    hxBs hxL hxcoord hac hJ₁L hJ₁Z hJ₁ hα hgN hg hb' hN hJ₁N hJ₂N hBsN hjoin
  have hJ₁perf : ⁅J₁, J₁⁆ = J₁ := Subgroup.commutator_eq_self
  have hJ₂perf : ⁅J₁.map (MulAut.conj g).toMonoidHom, J₁.map (MulAut.conj g).toMonoidHom⁆ =
      J₁.map (MulAut.conj g).toMonoidHom := by
    rw [← Subgroup.map_commutator, hJ₁perf]
  refine qtwoDB43_case_orth_big_of (m := 6) hRig (by norm_num) hBsE hSC hinner hBsN hΛ hlab
    (Or.inr ⟨⟨3, rfl⟩, hlab6⟩)
    (ggQTwoDUnitSix_gamma hK hD hψk hε hBsE hSC hcard hω hind hpermβ hac hJ₁L hJ₁Z hJ₁ hα hgN hg
      hb' hN hJ₁N hJ₂N hBsN).1 hΘact hJ₁N hJ₁perf (s₁ := ⟨x, hxBs⟩) ?_ ?_ hJ₂N hJ₂perf
    (s₂ := α ⟨x, hxBs⟩) ?_ ?_
  · intro i _
    rw [hxcoord]
    exact one_ne_zero
  · intro n hn
    exact ((Subgroup.mem_centralizer_iff.mp hxL) n (hJ₁L hn)).symm
  · intro i _
    rw [hα, hxcoord, dSign_apply_vec]
    split_ifs
    · show (-1 : ZMod 3) ≠ 0
      decide
    · show (1 : ZMod 3) ≠ 0
      decide
  · intro n hn
    obtain ⟨j, hj, hjn⟩ := Subgroup.mem_map.mp hn
    have hxcomm : x * (j : G) = (j : G) * x :=
      ((Subgroup.mem_centralizer_iff.mp hxL) (j : G) (hJ₁L hj)).symm
    have hn_eq : (n : G) = g * (j : G) * g⁻¹ := by
      rw [← hjn]
      rfl
    rw [hg ⟨x, hxBs⟩, hn_eq]
    calc g * x * g⁻¹ * (g * (j : G) * g⁻¹) = g * (x * (j : G)) * g⁻¹ := by group
      _ = g * ((j : G) * x) * g⁻¹ := by rw [hxcomm]
      _ = g * (j : G) * g⁻¹ * (g * x * g⁻¹) := by group

end CFSG.StandardType.QTwo

end
