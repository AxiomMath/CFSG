module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixStd
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbrB
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMLin
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosurePComp

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnitSix_x_not_mem_centralizer_J₂ (hK : Nat.card K = 4) {L Bs : Subgroup G}
    {Q : Type} [Group Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) {x : G} (hxBs : x ∈ Bs)
    {βL : Additive ↥Bs ≃+ DVec 6} (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1)
    {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    {a c : Fin 6} (hac : a ≠ c) {J₁ : Subgroup G}
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) :
    x ∉ Subgroup.centralizer ((J₁.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  classical
  intro hxc
  have hyBs : g⁻¹ * x * g ∈ Bs := ((Subgroup.mem_normalizer_iff''.mp hgN) x).mp hxBs
  have hyc : g⁻¹ * x * g ∈ Subgroup.centralizer (J₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hgh : g * h * g⁻¹ ∈ J₁.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hxc) (g * h * g⁻¹) hgh
    calc h * (g⁻¹ * x * g) = g⁻¹ * ((g * h * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * h * g⁻¹)) * g := by rw [hcomm]
      _ = (g⁻¹ * x * g) * h := by group
  have hconst := ggQTwoDUnitSix_const_of_mem_centralizer hK hD hψk hω hind hJ₁
    (s := ⟨_, hyBs⟩) hyc
  have hαy : α ⟨_, hyBs⟩ = ⟨x, hxBs⟩ := by
    apply Subtype.ext
    rw [hg]
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group
  have hdS : dSign 6 a c (βL (Additive.ofMul (⟨_, hyBs⟩ : ↥Bs))) = fun _ => 1 := by
    rw [← hα, hαy, hxcoord]
  obtain ⟨k, hk⟩ : ∃ k, k ∈ (Finset.univ.erase c).erase a :=
    Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩),
        Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
      norm_num)
  have hka : k ≠ a := (Finset.mem_erase.mp hk).1
  have hkc : k ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hyk := congrFun hdS k
  rw [dSign_apply_vec, if_neg (not_or.mpr ⟨hka, hkc⟩)] at hyk
  have hya := congrFun hdS a
  rw [dSign_apply_vec, if_pos (Or.inl rfl),
    hconst a (Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩) k (Finset.mem_erase.mp hk).2,
    hyk] at hya
  exact absurd hya (by decide)

theorem ggQTwoDUnitSix_nbr (hK : Nat.card K = 4) {B L Bs : Subgroup G} {Q : Type} [Group Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψr : ψ.range = NsQuot.img (Subgroup.normalizer (L : Set G)) f L)
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) {x : G} (hThmI : GGThmIHyp 3 B x L)
    (hBsE : CFSG.Open.IsElemAbelian 3 Bs) (hBBs : B ≤ Bs) (hxB : x ∈ B) (hxBs : x ∈ Bs)
    (hxord : orderOf x = 3) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    {βL : Additive ↥Bs ≃+ DVec 6} (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1)
    {ω : Kˣ} (hω : orderOf ω = 3)
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    {a c : Fin 6} (hac : a ≠ c) {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {b' : ↥Bs}
    (hb' : βL (Additive.ofMul b') = Pi.single c 1) (hb'B : (b' : G) ∈ B) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁N : J₁ ≤ N) (hJ₂N : J₁.map (MulAut.conj g).toMonoidHom ≤ N) :
    GGNbr 3 B x (Subgroup.closure {x, (b' : G)}) J₁ b' N := by
  have h5 : (Finset.univ.erase c).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  obtain ⟨θ, hθ, hθr, -⟩ := ggQTwoDUnitSix_chart hK hD hψk (Finset.univ.erase c) (by omega)
    hJ₁L hJ₁Z hJ₁
  have hpJ : 3 ∣ Nat.card ↥J₁ := ggQTwoDUnitSix_three_dvd_card hK (by omega) hθ hθr
  have hpJ₂ : 3 ∣ Nat.card ↥(J₁.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hpJ
  have hJ₂q : CFSG.Assembly.IsQuasisimple ↥(J₁.map (MulAut.conj g).toMonoidHom) :=
    ggQTwoDUnitSix_J_quasisimple hK (Finset.univ.erase c) (by omega)
      (θ := (MulAut.conj g).toMonoidHom.comp θ) ((MulAut.conj g).injective.comp hθ)
      (by rw [MonoidHom.range_comp, hθr])
  have hDJ := ggQTwoDUnitSix_stdSub hK hD hψr hψk hBsE hBBs hxB hxBs hxord hxL hxcoord hω hind
    hJ₁L hJ₁Z hJ₁ hb' hb'B
  have hxJ₂ : x ∈ Subgroup.normalizer
      ((J₁.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
    qtwoDB17_mem_normalizer_map_conj
      (ggQTwoDUnitSix_Bs_le_normalizer hK hD hψk hind (by omega) hJ₁L hJ₁Z hJ₁) hgN hxBs
  refine ggNbr_of_pComponent hThmI hDJ hpJ rfl hN hJ₁N
    (le_iSup_conj_pLayer_of_pComponent hN hJ₁N Subgroup.commutator_eq_self hpJ) fun hxO => ?_
  have hcop : Nat.Coprime 3 (Nat.card (LargeEvenPPrimeCoreOf 3 N)) := by
    rw [LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective N.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hcen := mem_centralizer_of_commutator_le_coprime Nat.prime_three hJ₂q hpJ₂ hcop
    (fun j hj => mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer (hJ₂N hj))) hxJ₂
    ((Subgroup.commutator_mono hJ₂N le_rfl).trans hxO)
  exact ggQTwoDUnitSix_x_not_mem_centralizer_J₂ hK hD hψk hxBs hxcoord hω hind hac hJ₁ hα hgN hg
    hcen

end CFSG.StandardType.QTwo

end
