module

public import CFSG.Quasithin.EmptyFaithful.SzN16TwoRed
public import CFSG.Quasithin.EmptyFaithful.S153D0JCase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S153D
open scoped commutatorElement

private theorem mem_normalizer_sup_szn16 {G : Type} [Group G] {L R : Subgroup G} {g : G}
    (hL : g ∈ Subgroup.normalizer (L : Set G)) (hR : g ∈ Subgroup.normalizer (R : Set G)) :
    g ∈ Subgroup.normalizer ((L ⊔ R : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (L : Set G), g ∈ Subgroup.normalizer (R : Set G) →
      ∀ u ∈ L ⊔ R, g * u * g⁻¹ ∈ L ⊔ R := by
    intro g hgL hgR u hu
    have hle : L ⊔ R ≤ (L ⊔ R).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hgL x).1 hx)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 hgR x).1 hx)
    exact hle hu
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hL hR h, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hL) (inv_mem hR) _ hh
  simpa [mul_assoc] using this

theorem input15316One_of_a3 (h37 : A37ForSQTK) (h38 : A38ForSQTK) : Input15316One := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hRL hO _hdesc
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hI : IsHPlus Yp (Sgp153 T V₁) M I := c.ctx.inH
  have hF : Facts15311 T M V₁ Yp I := c.facts
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1
  have hLn : ¬ L ≤ M ⊓ I := c.conc.2.1
  have hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := c.conc.2.2.2.2.2
  have hRp : IsPGroup 2 (R153 T V₁ Yp) := pCoreOf_isPGroup 2 _
  have hVR : R153 T V₁ Yp ≤ Subgroup.centralizer (VZ T M : Set G) := by
    rw [hF.R_eq]
    exact inf_le_right
  have hWc := S153D.WL_le_centerOf hh c.ctx hF hLI hO
  have hqa := S153D.isQuasisimple_autOn_WL hh c.ctx hF hLI hLn hLq hRL hO
  have h1 := SzN16.isTwoReducedIn_conjClosure_sup hRp hRL (perfect_of_mem_cComp hLI) hLq hO hVR
    hh.hyp.elemAbelian hWc hqa
  refine ⟨h1, ?_⟩
  set R : Subgroup G := R153 T V₁ Yp with hRdef
  set H₁ : Subgroup G := L ⊔ R with hH₁
  set W : Subgroup G := WL153 T M L with hWdef
  set C : Subgroup G := Subgroup.centralizer (W : Set G) with hC
  have hYI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hYL : Yp ≤ Subgroup.normalizer (L : Set G) := S153D.Yp_le_normalizer h37 h38 hh hI hLI
  have hYR : Yp ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf 2 (Yp ⊔ Sgp153 T V₁))
  have hYH₁ : Yp ≤ Subgroup.normalizer (H₁ : Set G) := fun y hy =>
    mem_normalizer_sup_szn16 (hYL hy) (hYR hy)
  have hYM : Yp ≤ M ⊓ I := hF.norm_eq ▸ le_inf hYI Subgroup.le_normalizer
  have hMV : M = Subgroup.normalizer (VZ T M : Set G) := hh.hyp.isHv_of_inM' hh.hyp.inM
  have hYW : Yp ≤ Subgroup.normalizer (W : Set G) := fun y hy =>
    SzN16.mem_normalizer_conjClosure (hYL hy) (hMV ▸ (hYM hy).1)
  refine ⟨h1.1.trans le_sup_left, sup_le h1.2.1 hYW, h1.2.2.1, ?_⟩
  intro D hDH hDN hD
  have hD₁ : D ⊓ H₁ ≤ C := by
    refine h1.2.2.2 (D ⊓ H₁) inf_le_right ?_ (fun d hd => hD d hd.1)
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hDN (Subgroup.mem_sup_left hg), Subgroup.le_normalizer hg⟩
  intro d hd
  obtain ⟨k, hk⟩ := hD d hd
  obtain ⟨a, ha, b, hb, hab⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hYH₁).1 (hDH hd)
  have hbN : b ∈ Subgroup.normalizer (H₁ : Set G) := hYH₁ hb
  have hPY : pCoreOf 2 Yp ≤ R :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Yp).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 Yp) fun s hs =>
        normalizer_le_normalizer_pCoreOf 2 Yp (S153D.Sgp153_le_normalizer_Yp hh hs))
      (pCoreOf_isPGroup 2 Yp)
  have hb3 : b ^ 3 ∈ H₁ := Subgroup.mem_sup_right (hPY (SzN16.pow_three_mem_pCoreOf hF hb))
  have hd3 : d ^ 3 ∈ H₁ := by
    have e : d ^ 3 = a * (b * a * b⁻¹) * (b * (b * a * b⁻¹) * b⁻¹) * b ^ 3 := by
      rw [hab]
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e]
    have h1' : b * a * b⁻¹ ∈ H₁ := (Subgroup.mem_normalizer_iff.1 hbN a).1 ha
    have h2' : b * (b * a * b⁻¹) * b⁻¹ ∈ H₁ := (Subgroup.mem_normalizer_iff.1 hbN _).1 h1'
    exact H₁.mul_mem (H₁.mul_mem (H₁.mul_mem ha h1') h2') hb3
  have hd3C : d ^ 3 ∈ C := hD₁ ⟨D.pow_mem hd 3, hd3⟩
  exact SzN16.mem_of_pow_mem_of_coprime
    (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)) hd3C hk

end CFSG.Quasithin
