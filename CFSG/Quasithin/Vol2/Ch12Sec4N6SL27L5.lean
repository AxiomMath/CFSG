module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6E

public section

namespace CFSG.Quasithin.H13
namespace N1246
open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative Pointwise commutatorElement
variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem sl27l5_mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ h : G, h ∈ Subgroup.normalizer (A : Set G) → h ∈ Subgroup.normalizer (B : Set G) →
      ∀ x ∈ ⁅A, B⁆, h * x * h⁻¹ ∈ ⁅A, B⁆ := by
    intro h hhA hhB x hx
    rw [Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hs
      have hA' : h * a * h⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hhA a).1 ha
      have hB' : h * b * h⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hhB b).1 hb
      have e : h * ⁅a, b⁆ * h⁻¹ = ⁅h * a * h⁻¹, h * b * h⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator hA' hB'
    | one => simp
    | mul a b _ _ ha hb =>
      have := Subgroup.mul_mem _ ha hb
      simpa [mul_assoc] using this
    | inv a _ ha =>
      have := Subgroup.inv_mem _ ha
      simpa [mul_assoc] using this
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hA hB x hx, fun hx => ?_⟩
  have h1 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ ⁅A, B⁆ :=
    key g⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) (g * x * g⁻¹) hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rw [e] at h1
  exact h1

omit [Finite G] in
private theorem sl27l5_comm_mul_right {d l q : G} (hdl : d * l = l * d) :
    ⁅d, l * q⁆ = l * ⁅d, q⁆ * l⁻¹ := by
  simp only [commutatorElement_def]
  calc d * (l * q) * d⁻¹ * (l * q)⁻¹ = d * l * q * d⁻¹ * q⁻¹ * l⁻¹ := by group
    _ = l * d * q * d⁻¹ * q⁻¹ * l⁻¹ := by rw [hdl]
    _ = l * (d * q * d⁻¹ * q⁻¹) * l⁻¹ := by group

omit [Finite G] in
private theorem sl27l5_comm_left_mul {e d r : G} (he : e * (d * r * d⁻¹) = d * r * d⁻¹ * e) :
    ⁅e * d, r⁆ = ⁅d, r⁆ := by
  simp only [commutatorElement_def]
  calc e * d * r * (e * d)⁻¹ * r⁻¹ = e * (d * r * d⁻¹) * e⁻¹ * r⁻¹ := by group
    _ = d * r * d⁻¹ * e * e⁻¹ * r⁻¹ := by rw [he]
    _ = d * r * d⁻¹ * r⁻¹ := by group

theorem commutator_D_Q_eq_bot {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V]
    (c : Ctx T L V E z v)
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hL1 : Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (c.L1 : Set G))
    (hEx : ∀ k ∈ c.R1 ⊓ Subgroup.centralizer (c.L1 : Set G),
      ∃ e ∈ E, ∃ d ∈ T ⊓ Subgroup.centralizer (L : Set G), k = e * d) :
    ⁅T ⊓ Subgroup.centralizer (L : Set G), pCoreOf 2 (L ⊔ T)⁆ = ⊥ := by
  have hyp := c.cx.hyp
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T := c.Q_le_R1.trans c.R1_le_T
  have hLsup : L ≤ L ⊔ T := le_sup_left
  have hTsup : T ≤ L ⊔ T := le_sup_right
  have hLD : L ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro l hl
    refine Subgroup.centralizer_le_normalizer
      ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)
      (Subgroup.mem_centralizer_iff.2 fun d hd => ?_)
    exact (Subgroup.mem_centralizer_iff.1 hd.2 l hl).symm
  have hTD : T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    fun t ht => CFSG.Quasithin.A4.mem_normalizer_inf (Subgroup.le_normalizer ht)
      (CFSG.Quasithin.F7.normalizer_le_normalizer_centralizer L (hyp.normalizes ht))
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer ((pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hLQ := hLsup.trans hLTQ
  have hTQ := hTsup.trans hLTQ
  have hLTcomm : L ⊔ T ≤ Subgroup.normalizer
      ((⁅T ⊓ Subgroup.centralizer (L : Set G), pCoreOf 2 (L ⊔ T)⁆ : Subgroup G) : Set G) :=
    sup_le (fun l hl => sl27l5_mem_normalizer_commutator (hLD hl) (hLQ hl))
      (fun t ht => sl27l5_mem_normalizer_commutator (hTD ht) (hTQ ht))
  have hPT : ⁅T ⊓ Subgroup.centralizer (L : Set G), pCoreOf 2 (L ⊔ T)⁆ ≤ T := by
    refine Subgroup.commutator_le.2 fun d hd q hq => ?_
    rw [commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem hd.1 (hQT hq)) (T.inv_mem hd.1)) (T.inv_mem (hQT hq))
  have hlow : ⁅T ⊓ Subgroup.centralizer (L : Set G), pCoreOf 2 (L ⊔ T)⁆ ≤
      ⁅c.R1 ⊓ Subgroup.centralizer (c.L1 : Set G), c.R1⁆ :=
    Subgroup.commutator_mono c.CTL_le_CR1L1 c.Q_le_R1
  have hup : ⁅c.R1 ⊓ Subgroup.centralizer (c.L1 : Set G), c.R1⁆ ≤
      ⁅T ⊓ Subgroup.centralizer (L : Set G), pCoreOf 2 (L ⊔ T)⁆ := by
    refine Subgroup.commutator_le.2 fun k hk r hr => ?_
    obtain ⟨e, he, d, hd, rfl⟩ := hEx k hk
    have hsC : d * r * d⁻¹ ∈ Subgroup.centralizer (E : Set G) :=
      (Subgroup.mem_normalizer_iff.1
        (CFSG.Quasithin.F7.normalizer_le_normalizer_centralizer E (c.TE hd.1)) r).1 hr.2
    have he' : e * (d * r * d⁻¹) = d * r * d⁻¹ * e := Subgroup.mem_centralizer_iff.1 hsC e he
    rw [sl27l5_comm_left_mul he']
    obtain ⟨l, hl, hlq⟩ := CFSG.Quasithin.H13.cx_mem_mul_of_mem_T c.f c.Tbar hr.1
    have hqQ : l⁻¹ * r ∈ pCoreOf 2 (L ⊔ T) := by
      rw [c.Q]
      exact hlq
    obtain ⟨q, hq, hrq⟩ : ∃ q ∈ pCoreOf 2 (L ⊔ T), r = l * q :=
      ⟨l⁻¹ * r, hqQ, (mul_inv_cancel_left l r).symm⟩
    rw [hrq]
    have hdl : d * l = l * d := (Subgroup.mem_centralizer_iff.1 hd.2 l hl.2).symm
    rw [sl27l5_comm_mul_right hdl]
    have hlN := hLTcomm (hLsup hl.2)
    exact (Subgroup.mem_normalizer_iff.1 hlN (⁅d, q⁆)).1
      (Subgroup.commutator_mem_commutator hd hq)
  have hcomm : ⁅c.R1 ⊓ Subgroup.centralizer (c.L1 : Set G), c.R1⁆ =
      ⁅T ⊓ Subgroup.centralizer (L : Set G), pCoreOf 2 (L ⊔ T)⁆ := le_antisymm hup hlow
  by_contra hne
  have h2P : IsPGroup 2 ↥⁅T ⊓ Subgroup.centralizer (L : Set G), pCoreOf 2 (L ⊔ T)⁆ :=
    hyp.sylow.1.to_le hPT
  have hNP := CFSG.Quasithin.H13.Ch4.isUniqueM_normalizer_le c.uniq hne h2P hLTcomm
  have hR1N : Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer
      ((⁅T ⊓ Subgroup.centralizer (L : Set G), pCoreOf 2 (L ⊔ T)⁆ : Subgroup G) : Set G) := by
    intro g hg
    rw [← hcomm]
    exact sl27l5_mem_normalizer_commutator
      (CFSG.Quasithin.A4.mem_normalizer_inf hg
        (CFSG.Quasithin.F7.normalizer_le_normalizer_centralizer c.L1 (hL1 hg))) hg
  exact hN (hR1N.trans hNP)

end N1246
end CFSG.Quasithin.H13
end
