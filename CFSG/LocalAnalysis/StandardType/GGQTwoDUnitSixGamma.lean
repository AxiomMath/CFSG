module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigS5
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixDispU

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnitSix_gamma (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type} [Group Q]
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
    (hBsN : Bs ≤ Subgroup.normalizer (N : Set G)) :
    (∀ s : ↥Bs, ggGamma N hBsN s = 1 ↔ ∀ k : Fin 6, k ≠ c → βL (Additive.ofMul s) k = 0) ∧
      Nat.card (ggGamma N hBsN).range = 3 ^ (6 - 1) ∧ IsElemAbelian 3 (ggGamma N hBsN).range ∧
        (ggGamma N hBsN).range ≤ (MulAut.conj : ↥N →* MulAut ↥N).range ∧
          GGTorusSelfCent 3 (ggGamma N hBsN).range := by
  have hb'N : (b' : G) ∈ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact Subgroup.mem_centralizer_singleton_iff.mp (hN.1 hn)
  exact qtwoDB36_gamma_of (by norm_num) hBsE hSC hcard hb' hb'N
    (fun s hs hsC => ggQTwoDUnitSix_cent_E hK hD hψk hω hind hac hJ₁ hα hgN hg hs
      (Subgroup.centralizer_le hJ₁N hsC) (Subgroup.centralizer_le hJ₂N hsC))
    (ggQTwoDUnitSix_inner_N hK hD hψk hε hind hpermβ hac hJ₁L hJ₁Z hJ₁ hα hg hb' hN hJ₁N hJ₂N)
    hBsN

theorem ggQTwoDUnitSix_weyl_embed (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type}
    [Group Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
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
      ∀ s : ↥Bs, βL (Additive.ofMul (a s)) = w (βL (Additive.ofMul s))) :
    ∃ Θ : ↥(dEvenStab 6 (Pi.single c 1)) →*
        ↥(ggAutomizer (MulAut.conj : ↥N →* MulAut ↥N).range (ggGamma N hBsN).range),
      Function.Injective Θ ∧ ∀ (w : ↥(dEvenStab 6 (Pi.single c 1))) (s : ↥Bs),
        (Θ w : MulAut ↥(ggGamma N hBsN).range) ((ggGamma N hBsN).rangeRestrict s) =
          (ggGamma N hBsN).rangeRestrict (Additive.toMul (βL.symm
            ((w : DVec 6 ≃ₗ[ZMod 3] DVec 6) (βL (Additive.ofMul s))))) := by
  have hb'N : (b' : G) ∈ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact Subgroup.mem_centralizer_singleton_iff.mp (hN.1 hn)
  refine qtwoDB36_weyl_embed_of hBsN
    (ggQTwoDUnitSix_gamma hK hD hψk hε hBsE hSC hcard hω hind hpermβ hac hJ₁L hJ₁Z hJ₁ hα hgN hg
      hb' hN hJ₁N hJ₂N hBsN).1 fun w hw => ?_
  obtain ⟨a', -, ha'w⟩ := hjoin w hw.1
  exact ⟨a', ggAutomizer_mono Bs (sup_le hJ₁N hJ₂N)
    (ggQTwoDUnitSix_weyl_X hK hD hψk hε hind hpermβ hxBs hxL hxcoord hac hJ₁L hJ₁Z hJ₁ hb'
      (Subgroup.centralizer_le hJ₁N hb'N) hα hgN hg hw.1 hw.2 ha'w), ha'w⟩

theorem ggQTwoDUnitSix_torus_N (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type}
    [Group Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
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
    (hZ : Subgroup.center ↥N = ⊥) :
    ∃ τ : Multiplicative (DVec 6) →* ↥N,
      (∀ v : DVec 6, τ (Multiplicative.ofAdd v) = 1 ↔ ∀ i, i ≠ c → v i = 0) ∧
      (∀ (s : ↥Bs) (n : ↥N), ggGamma N hBsN s n =
        τ (Multiplicative.ofAdd (βL (Additive.ofMul s))) * n *
          (τ (Multiplicative.ofAdd (βL (Additive.ofMul s))))⁻¹) ∧
      (∀ z : ↥N, (∀ v : DVec 6, z * τ (Multiplicative.ofAdd v) = τ (Multiplicative.ofAdd v) * z) →
        z ^ 3 = 1 → z ∈ τ.range) ∧
      (∀ w ∈ dEvenStab 6 (Pi.single c 1), ∃ y : ↥N, ∀ v : DVec 6,
        y * τ (Multiplicative.ofAdd v) * y⁻¹ = τ (Multiplicative.ofAdd (w v))) ∧
      (∀ n : ↥N, (n : G) ∈ J₁ →
        n * τ (Multiplicative.ofAdd (fun _ => 1)) = τ (Multiplicative.ofAdd (fun _ => 1)) * n) ∧
      (∀ n : ↥N, (n : G) ∈ J₁.map (MulAut.conj g).toMonoidHom →
        n * τ (Multiplicative.ofAdd (dSign 6 a c (fun _ => 1))) =
          τ (Multiplicative.ofAdd (dSign 6 a c (fun _ => 1))) * n) := by
  obtain ⟨hker_char, -, -, hInner, hSelf⟩ := ggQTwoDUnitSix_gamma hK hD hψk hε hBsE hSC hcard hω
    hind hpermβ hac hJ₁L hJ₁Z hJ₁ hα hgN hg hb' hN hJ₁N hJ₂N hBsN
  obtain ⟨Θ, -, hΘact⟩ := ggQTwoDUnitSix_weyl_embed hK hD hψk hε hBsE hSC hcard hω hind hpermβ
    hxBs hxL hxcoord hac hJ₁L hJ₁Z hJ₁ hα hgN hg hb' hN hJ₁N hJ₂N hBsN hjoin
  obtain ⟨τ, hτker, hconj, hsc, hW, hcomm⟩ :=
    qtwoDB44_torus_of hBsN hZ hker_char hInner hSelf hΘact
  refine ⟨τ, hτker, hconj, hsc, hW, ?_, ?_⟩
  · intro n hn
    have hxcomm : x * (n : G) = (n : G) * x :=
      ((Subgroup.mem_centralizer_iff.mp hxL) (n : G) (hJ₁L hn)).symm
    have h := hcomm ⟨x, hxBs⟩ n hxcomm
    rwa [hxcoord] at h
  · intro n hn
    obtain ⟨j, hj, hjn⟩ := Subgroup.mem_map.mp hn
    have hxcomm : x * (j : G) = (j : G) * x :=
      ((Subgroup.mem_centralizer_iff.mp hxL) (j : G) (hJ₁L hj)).symm
    have hn_eq : (n : G) = g * (j : G) * g⁻¹ := by
      rw [← hjn]
      rfl
    have hαcomm : ((α ⟨x, hxBs⟩ : ↥Bs) : G) * n = n * ((α ⟨x, hxBs⟩ : ↥Bs) : G) := by
      rw [hg ⟨x, hxBs⟩, hn_eq]
      calc g * x * g⁻¹ * (g * (j : G) * g⁻¹) = g * (x * (j : G)) * g⁻¹ := by group
        _ = g * ((j : G) * x) * g⁻¹ := by rw [hxcomm]
        _ = g * (j : G) * g⁻¹ * (g * x * g⁻¹) := by group
    have h := hcomm (α ⟨x, hxBs⟩) n hαcomm
    have hαβ : βL (Additive.ofMul (α ⟨x, hxBs⟩)) = dSign 6 a c (fun _ => 1) := by
      rw [hα, hxcoord]
    rwa [hαβ] at h

end CFSG.StandardType.QTwo

end
