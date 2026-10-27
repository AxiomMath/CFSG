module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BlockNatural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TIFusion
public import CFSG.LocalAnalysis.UniquenessCase.UC22Main1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.PartTwo
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

theorem pCoreOf_L_le_T (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) :
    CFSG.Open.pCoreOf 2 c.L ≤ D.T := by
  have hnorm : ∀ n ∈ c.L ⊔ D.T, ∀ k ∈ c.L, n * k * n⁻¹ ∈ c.L := by
    intro n hn k hk
    exact (Subgroup.mem_normalizer_iff.mp
      ((sup_le (Subgroup.le_normalizer (H := c.L)) c.hL.1.1) hn) k).1 hk
  have hO2L_le_O2S : CFSG.Open.pCoreOf 2 c.L ≤
      CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) :=
    uc22main1_le_pCoreOf (K := c.L ⊔ D.T) (P := CFSG.Open.pCoreOf 2 c.L)
      ((uc22main1_pCoreOf_le c.L).trans le_sup_left)
      (uc22main1_isPGroup_pCoreOf c.L)
      (fun n hn x hx => uc22main1_conj_mem_pCoreOf hnorm hn hx)
  exact hO2L_le_O2S.trans
    (CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (CFSG.ABGLocalTools.isSylowOf_iff.mp
        (D.sylowG.of_le (le_sup_right : D.T ≤ c.L ⊔ D.T) le_top)))

theorem alpha_conj_of_inducedBar (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)}
    {κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV
      (CFSG.Open.pRank 2 D.Z)}
    (hker : CFSG.pCore 2 ↥c.L ≤ κ.α.ker)
    {x : G} (hx : x ∈ Subgroup.normalizer (c.L : Set G))
    {ℓ : Bar2 c.L} {l₀ : ↥c.L} (hl₀ : QuotientGroup.mk l₀ = ℓ)
    (hθ : InducedBar c.L x (MulAut.conj ℓ)) (l : ↥c.L) :
    κ.α ⟨x * (l : G) * x⁻¹,
        (Subgroup.mem_normalizer_iff.mp hx (l : G)).mp l.2⟩ =
      κ.α l₀ * κ.α l * (κ.α l₀)⁻¹ := by
  let l' : ↥c.L :=
    ⟨x * (l : G) * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx (l : G)).mp l.2⟩
  change κ.α l' = κ.α l₀ * κ.α l * (κ.α l₀)⁻¹
  have hθl : ℓ * QuotientGroup.mk l * ℓ⁻¹ = QuotientGroup.mk l' := by
    simpa only [MulAut.conj_apply] using hθ l l' rfl
  have hab : QuotientGroup.mk (s := CFSG.pCore 2 ↥c.L) l' =
      QuotientGroup.mk (s := CFSG.pCore 2 ↥c.L) (l₀ * l * l₀⁻¹) := by
    rw [← hθl, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hl₀]
  have hdiff : l'⁻¹ * (l₀ * l * l₀⁻¹) ∈ κ.α.ker :=
    hker (QuotientGroup.eq.mp hab)
  have hα : κ.α l' = κ.α (l₀ * l * l₀⁻¹) := by
    have h := hdiff
    rw [MonoidHom.mem_ker, map_mul, map_inv] at h
    exact inv_mul_eq_one.mp h
  rw [hα, map_mul, map_mul, map_inv]

end Ctx23L

theorem inducedBar_one {L : Subgroup G} : InducedBar L (1 : G) 1 := by
  intro l l' hll'
  have h : l' = l := Subtype.ext (by simpa using hll')
  subst h
  simp

theorem inducedBar_pow {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) {θ : MulAut (Bar2 L)}
    (h : InducedBar L x θ) (k : ℕ) : InducedBar L (x ^ k) (θ ^ k) := by
  induction k with
  | zero => simpa using (inducedBar_one (L := L))
  | succ k ih =>
      intro l l' hll'
      let l₂ : ↥L :=
        ⟨x * (l : G) * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx (l : G)).mp l.2⟩
      have hxk : (l' : G) = x ^ k * (l₂ : G) * (x ^ k)⁻¹ := by
        rw [show (l' : G) = x ^ (k + 1) * (l : G) * (x ^ (k + 1))⁻¹ from hll']
        rw [show (l₂ : G) = x * (l : G) * x⁻¹ from rfl, pow_succ]
        group
      have h1 := h l l₂ rfl
      have h2 := ih l₂ l' hxk
      calc (θ ^ (k + 1)) (QuotientGroup.mk l)
          = (θ ^ k) (θ (QuotientGroup.mk l)) := by
            rw [pow_succ]
            rfl
        _ = (θ ^ k) (QuotientGroup.mk l₂) := by rw [h1]
        _ = QuotientGroup.mk l' := h2

theorem inducedBar_mul {L : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G))
    {θ φ : MulAut (Bar2 L)} (hθ : InducedBar L x θ) (hφ : InducedBar L y φ) :
    InducedBar L (x * y) (θ * φ) := by
  intro l l' hll'
  let l₁ : ↥L :=
    ⟨y * (l : G) * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy (l : G)).mp l.2⟩
  have hφl := hφ l l₁ rfl
  have hxyl' : (l' : G) = x * (l₁ : G) * x⁻¹ := by
    rw [show (l' : G) = (x * y) * (l : G) * (x * y)⁻¹ from hll']
    rw [show (l₁ : G) = y * (l : G) * y⁻¹ from rfl]
    group
  have hθl := hθ l₁ l' hxyl'
  change θ (φ (QuotientGroup.mk l)) = QuotientGroup.mk l'
  rw [hφl, hθl]

theorem inducedBar_inv {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) {θ : MulAut (Bar2 L)}
    (h : InducedBar L x θ) : InducedBar L x⁻¹ θ⁻¹ := by
  intro l l' hll'
  have hxl' : (l : G) = x * (l' : G) * x⁻¹ := by
    rw [show (l' : G) = x⁻¹ * (l : G) * (x⁻¹)⁻¹ from hll']
    group
  have hh := h l' l hxl'
  change θ⁻¹ (QuotientGroup.mk l) = QuotientGroup.mk l'
  rw [← hh, MulAut.inv_apply_self]

theorem inducedBar_of_mem {L : Subgroup G} (g : ↥L) :
    InducedBar L (g : G) (MulAut.conj (QuotientGroup.mk g : Bar2 L)) := by
  intro l l' hll'
  rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext hll'.symm

theorem inducedBar_unique {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) {θ θ' : MulAut (Bar2 L)}
    (h : InducedBar L x θ) (h' : InducedBar L x θ') : θ = θ' := by
  ext q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) q
  let l' : ↥L :=
    ⟨x * (l : G) * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx (l : G)).mp l.2⟩
  have h1 := h l l' rfl
  have h2 := h' l l' rfl
  exact h1.trans h2.symm

theorem inducedBar_conj {L : Subgroup G} {g x : G} (hg : g ∈ L)
    (hx : x ∈ Subgroup.normalizer (L : Set G)) {ℓ : Bar2 L}
    (h : InducedBar L x (MulAut.conj ℓ)) :
    InducedBar L (g * x * g⁻¹)
      (MulAut.conj ((QuotientGroup.mk ⟨g, hg⟩ : Bar2 L) * ℓ *
        (QuotientGroup.mk ⟨g, hg⟩ : Bar2 L)⁻¹)) := by
  let gL : ↥L := ⟨g, hg⟩
  let q : Bar2 L := QuotientGroup.mk gL
  intro l l' hll'
  let l₁ : ↥L :=
    ⟨g⁻¹ * (l : G) * g, L.mul_mem (L.mul_mem (L.inv_mem hg) l.2) hg⟩
  let l₁' : ↥L :=
    ⟨g⁻¹ * (l' : G) * g, L.mul_mem (L.mul_mem (L.inv_mem hg) l'.2) hg⟩
  have hrel : (l₁' : G) = x * (l₁ : G) * x⁻¹ := by
    rw [show (l₁' : G) = g⁻¹ * (l' : G) * g from rfl,
      show (l₁ : G) = g⁻¹ * (l : G) * g from rfl, hll']
    group
  have h1 := h l₁ l₁' hrel
  simp only [MulAut.conj_apply] at h1
  have hq : ℓ * (QuotientGroup.mk l₁ : Bar2 L) * ℓ⁻¹ =
      (QuotientGroup.mk l₁' : Bar2 L) := h1
  have e1 : (QuotientGroup.mk l : Bar2 L) = q * (QuotientGroup.mk l₁ : Bar2 L) * q⁻¹ := by
    rw [show l = gL * l₁ * gL⁻¹ from by ext; simp [gL, l₁]; group]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have e2 : (QuotientGroup.mk l' : Bar2 L) =
      q * (QuotientGroup.mk l₁' : Bar2 L) * q⁻¹ := by
    rw [show l' = gL * l₁' * gL⁻¹ from by ext; simp [gL, l₁']; group]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [e1, e2]
  change (MulAut.conj (q * ℓ * q⁻¹)) (q * (QuotientGroup.mk l₁ : Bar2 L) * q⁻¹) =
    q * (QuotientGroup.mk l₁' : Bar2 L) * q⁻¹
  rw [MulAut.conj_apply]
  calc (q * ℓ * q⁻¹) * (q * (QuotientGroup.mk l₁ : Bar2 L) * q⁻¹) *
        (q * ℓ * q⁻¹)⁻¹
      = q * (ℓ * (QuotientGroup.mk l₁ : Bar2 L) * ℓ⁻¹) * q⁻¹ := by group
    _ = q * (QuotientGroup.mk l₁' : Bar2 L) * q⁻¹ := by rw [hq]

theorem inducedBar_conj_pow {L : Subgroup G} {a : G}
    (hL : a ∈ Subgroup.normalizer (L : Set G))
    {ℓ : Bar2 L} (hθ : InducedBar L a (MulAut.conj ℓ)) (t : ↥L) (k : ℕ) :
    InducedBar L (((t : G) * a * (t : G)⁻¹) ^ k)
      (MulAut.conj ((QuotientGroup.mk t * ℓ * (QuotientGroup.mk t)⁻¹) ^ k)) := by
  have htN : (t : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer t.2
  have h₁ : InducedBar L ((t : G) * a * (t : G)⁻¹)
      (MulAut.conj (QuotientGroup.mk t * ℓ * (QuotientGroup.mk t)⁻¹)) :=
    inducedBar_conj t.2 hL hθ
  have hnorm : (t : G) * a * (t : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hL) (Subgroup.inv_mem _ htN)
  have hpow := inducedBar_pow hnorm h₁ k
  simpa only [map_pow] using hpow

theorem inducedBar_conj_pow_eq_one {L : Subgroup G} {n : ℕ} {a : G}
    (hL : a ∈ Subgroup.normalizer (L : Set G))
    {ℓ : Bar2 L} (hθ : InducedBar L a (MulAut.conj ℓ))
    (hpow : a ^ n = 1) :
    (MulAut.conj ℓ) ^ n = 1 := by
  have hθpow : InducedBar L (a ^ n) ((MulAut.conj ℓ) ^ n) :=
    inducedBar_pow hL hθ n
  rw [hpow] at hθpow
  exact inducedBar_unique (Subgroup.one_mem _) hθpow inducedBar_one

theorem inducedBar_one_of_conj_mem {L : Subgroup G} {g x : G} (hg : g ∈ L)
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    (h : InducedBar L (g * x * g⁻¹) 1) : InducedBar L x 1 := by
  have hgN : g ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hg
  have hginvN : g⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hgN
  have hgxgN : g * x * g⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (mul_mem hgN hx) hginvN
  have hgInd : InducedBar L g (MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : Bar2 L)) :=
    inducedBar_of_mem ⟨g, hg⟩
  have hginvInd : InducedBar L g⁻¹
      (MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : Bar2 L))⁻¹ :=
    inducedBar_inv hgN hgInd
  have h1 : InducedBar L (g⁻¹ * (g * x * g⁻¹))
      ((MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : Bar2 L))⁻¹ * 1) :=
    inducedBar_mul hginvN hgxgN hginvInd h
  have h2 : InducedBar L ((g⁻¹ * (g * x * g⁻¹)) * g)
      (((MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : Bar2 L))⁻¹ * 1) *
        MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : Bar2 L)) :=
    inducedBar_mul (mul_mem hginvN hgxgN) hgN h1 hgInd
  have hx' : (g⁻¹ * (g * x * g⁻¹)) * g = x := by group
  have hauto : ((MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : Bar2 L))⁻¹ * 1) *
        MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : Bar2 L) = 1 := by group
  simpa [hx', hauto] using h2

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
