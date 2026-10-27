module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35TB4Fin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35TB4Blk
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35TB4Phi
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2That
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.TB4

open S35.Std S35.Fin S35.Ch S35.Ch2 S35.II
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem forall_of_sup {Q A B : Subgroup G} {K : Type} [Group K] (hsup : A ⊔ B = Q)
    (φ : ↥Q →* K) (W : Subgroup K)
    (hA : ∀ (q : G) (hq : q ∈ Q), q ∈ A → φ ⟨q, hq⟩ ∈ W)
    (hB : ∀ (q : G) (hq : q ∈ Q), q ∈ B → φ ⟨q, hq⟩ ∈ W) : ∀ q : ↥Q, φ q ∈ W := by
  have hAQ : A ≤ Q := hsup ▸ le_sup_left
  have hBQ : B ≤ Q := hsup ▸ le_sup_right
  let K' : Subgroup G := (W.comap φ).map Q.subtype
  have hA' : A ≤ K' := fun q hq => ⟨⟨q, hAQ hq⟩, hA q (hAQ hq) hq, rfl⟩
  have hB' : B ≤ K' := fun q hq => ⟨⟨q, hBQ hq⟩, hB q (hBQ hq) hq, rfl⟩
  have hQK : Q ≤ K' := by rw [← hsup]; exact sup_le hA' hB'
  intro q
  obtain ⟨x, hx, hxq⟩ := hQK q.2
  have : x = q := Subtype.ext hxq
  subst this
  exact hx

theorem bar_That2_eq (hS : Sit H M S) (hTF : ThatFacts H M) {γ : Geo H M} (c : Chart2 γ)
    (hγ : vtype γ = false) {l : Geo H M} (hl : l ∈ nbrs γ) :
    c.bar (That2 γ l) = That (c.Dl l) := by
  obtain ⟨hQT, hTle, hidx⟩ := hTF γ l hγ hl
  have hD := c.card_Dl hS hl
  have h1 := c.card_bar hS hγ (A := stab γ ⊓ stab l) inf_le_left (S35.Ch.Qv_le_inf' hS hl)
  have h2 := c.card_bar hS hγ (A := That2 γ l) (hTle.trans inf_le_left) hQT
  have h4 := Subgroup.relIndex_mul_relIndex (Qv γ) (That2 γ l) (stab γ ⊓ stab l) hQT hTle
  have h3 : Nat.card (c.bar (stab γ ⊓ stab l)) = 8 := hD
  rw [← h1, ← h2, h3, hidx] at h4
  have hc : Nat.card (c.bar (That2 γ l)) = 4 := by omega
  exact Subgroup.eq_of_le_of_card_ge (c.bar_That2_le hS hγ hl)
    (by rw [S35.Ch.card_That hD, hc])

theorem thmBcase4_II (hS : Sit H M S) (hII : S35.CaseII H M) (hZB : ZvBlock H M)
    (hNTh : NbarThat H M) (hTF : ThatFacts H M) (h6 : ClaimS6 H M) : ThmBcase4 H M := by
  intro hNT γ la lb β α' hγ hla hlb hβ hβγ hα' hα'γ hnb _ r hr hrla _ _ hlbq hlaq
  have hla' : γ ∈ nbrs la := mem_nbrs_symm.mp hla
  have hlb' : γ ∈ nbrs lb := mem_nbrs_symm.mp hlb
  have hβ' : la ∈ nbrs β := mem_nbrs_symm.mp hβ
  have hα'' : lb ∈ nbrs α' := mem_nbrs_symm.mp hα'
  have vla : vtype la = true := vtype_nbr_S5 hγ hla
  have vlb : vtype lb = true := vtype_nbr_S5 hγ hlb
  have vβ : vtype β = false := vtype_nbr_S3 vla hβ
  have vα' : vtype α' = false := vtype_nbr_S3 vlb hα'
  have hTb : (Qv γ ⊓ Qv lb) ⊔ Qv α' ≤ That2 α' lb := hNT γ lb α' hγ hlb hα'' hα'γ
  have hTa : (Qv γ ⊓ Qv la) ⊔ Qv β ≤ That2 β la := hNT γ la β hγ hla hβ' hβγ
  have hZa : Zv β ≤ Vn γ := (Zv_le_Zv_of_nbr hS vβ hβ').trans (Zv_le_Vn hla)
  have hZb : Zv α' ≤ Vn γ := (Zv_le_Zv_of_nbr hS vα' hα'').trans (Zv_le_Vn hlb)
  have hNa : Qv γ ⊓ Qv la ≤ Nr γ r := fun q hq =>
    ⟨S35.Ch.Qv_le_stab' γ hq.1, hZa (hlaq q ⟨hq.2, (le_sup_left.trans hTa) hq⟩)⟩
  have hNb : Qv γ ⊓ Qv lb ≤ Nr γ r := fun q hq =>
    ⟨S35.Ch.Qv_le_stab' γ hq.1, hZb (hlbq q ⟨hq.2, (le_sup_left.trans hTb) hq⟩)⟩
  have hsup := Qv_inf_sup_eq hS hZB h6 hγ hla hlb hnb
  have hQ : Qv γ ≤ Nr γ r := hsup.symm.le.trans (sup_le hNa hNb)
  have hNa' : Qv β ⊓ Qv la ≤ Nr γ r := fun q hq =>
    ⟨Qv_le_stab hS hla' hq.2, hZa (hlaq q ⟨hq.2, (le_sup_right.trans hTa) hq.1⟩)⟩
  have hNb' : Qv α' ⊓ Qv lb ≤ Nr γ r := fun q hq =>
    ⟨Qv_le_stab hS hlb' hq.2, hZb (hlbq q ⟨hq.2, (le_sup_right.trans hTb) hq.1⟩)⟩
  have hTna : That2 γ la ≤ Nr γ r :=
    (hNTh β la γ vβ hβ' hla hβγ.symm).trans (sup_le hNa' hQ)
  have hTnb : That2 γ lb ≤ Nr γ r :=
    (hNTh α' lb γ vα' hα'' hlb hα'γ.symm).trans (sup_le hNb' hQ)
  obtain ⟨c⟩ := exists_chart2 hS hγ
  have hne : c.pt la ≠ c.pt lb := fun h => hnb ((c.sameBlock_iff hS hγ hla hlb).mpr h)
  set Φ := Phi c hS hγ r hQ with hΦ
  set W : Subgroup orth.W := Subgroup.zpowers (vp (c.pt la)) ⊔ Subgroup.zpowers (vp (c.pt lb))
    with hW
  have hmem : ∀ (l δ : Geo H M) (hl : l ∈ nbrs γ), Zv δ ≤ Zv l →
      ∀ (q : G) (hq : q ∈ Qv γ), ⁅q, r⁆ ∈ Zv δ →
        Φ ⟨q, hq⟩ ∈ Subgroup.zpowers (vp (c.pt l)) := by
    intro l δ hl hZ q hq hqr
    have := (c.mem_img_iff').mpr ⟨⟨⁅q, r⁆, (hQ hq).2⟩, hZ hqr, rfl⟩
    rw [c.img_Zv_nbr hS hγ hl] at this
    exact this
  have hrange : ∀ q : ↥(Qv γ), Φ q ∈ W := by
    refine forall_of_sup hsup Φ W ?_ ?_
    · intro q hq hqa
      refine Subgroup.mem_sup_left (hmem la β hla (Zv_le_Zv_of_nbr hS vβ hβ') q hq ?_)
      exact hlaq q ⟨hqa.2, (le_sup_left.trans hTa) hqa⟩
    · intro q hq hqb
      refine Subgroup.mem_sup_right (hmem lb α' hlb (Zv_le_Zv_of_nbr hS vα' hα'') q hq ?_)
      exact hlbq q ⟨hqb.2, (le_sup_left.trans hTb) hqb⟩
  have hinv : ∀ {l : Geo H M} (hl : l ∈ nbrs γ), That2 γ l ≤ Nr γ r →
      ∀ g ∈ That (c.Dl l), ∀ u ∈ Φ.range, orth.act g u ∈ Φ.range := by
    intro l hl hTn g hg u hu
    rw [← bar_That2_eq hS hTF c hγ hl] at hg
    obtain ⟨t, ht, rfl⟩ := c.mem_bar_iff.mp hg
    obtain ⟨⟨q, hq⟩, rfl⟩ := hu
    have htn : (t : G) ∈ Nr γ r := hTn ht
    exact ⟨⟨_, conj_mem_Qv t.2 hq⟩, (Phi_conj c hS hγ r hQ htn hq)⟩
  have hbot : Φ.range = ⊥ :=
    centre_trick (c.card_Dl hS hla) (c.card_Dl hS hlb) (c.isFixPt_pt hS hla)
      (c.isFixPt_pt hS hlb) hne (by rintro _ ⟨q, rfl⟩; exact hrange q)
      (hinv hla hTna) (hinv hlb hTnb)
  have hΦ1 : ∀ (q : G) (hq : q ∈ Qv γ), ⁅q, r⁆ ∈ Cb γ := by
    intro q hq
    have : Φ ⟨q, hq⟩ = 1 := by
      have h : Φ ⟨q, hq⟩ ∈ Φ.range := ⟨⟨q, hq⟩, rfl⟩
      rw [hbot] at h
      exact h
    exact (c.π_eq_one ⟨⁅q, r⁆, (hQ hq).2⟩).mp this
  have hca : ∀ q ∈ Qv γ ⊓ Qv la, q * r = r * q := by
    intro q hq
    have h1 : ⁅q, r⁆ ∈ Zv β := hlaq q ⟨hq.2, (le_sup_left.trans hTa) hq⟩
    have h2 : ⁅q, r⁆ ∈ Cb γ ⊓ Zv la := ⟨hΦ1 q hq.1, Zv_le_Zv_of_nbr hS vβ hβ' h1⟩
    rw [S34.Cb_inf_Zv_eq hS.glob hγ hla] at h2
    have h3 : ⁅q, r⁆ ∈ Zv β ⊓ Zv γ := ⟨h1, h2⟩
    rw [(Zv_ne hS vla hβ hla' hβγ).2.2, Subgroup.mem_bot] at h3
    have := h3
    rw [commutatorElement_def] at this
    calc q * r = (q * r * q⁻¹ * r⁻¹) * (r * q) := by group
      _ = r * q := by rw [this, one_mul]
  have hcb : ∀ q ∈ Qv γ ⊓ Qv lb, q * r = r * q := by
    intro q hq
    have h1 : ⁅q, r⁆ ∈ Zv α' := hlbq q ⟨hq.2, (le_sup_left.trans hTb) hq⟩
    have h2 : ⁅q, r⁆ ∈ Cb γ ⊓ Zv lb := ⟨hΦ1 q hq.1, Zv_le_Zv_of_nbr hS vα' hα'' h1⟩
    rw [S34.Cb_inf_Zv_eq hS.glob hγ hlb] at h2
    have h3 : ⁅q, r⁆ ∈ Zv α' ⊓ Zv γ := ⟨h1, h2⟩
    rw [(Zv_ne hS vlb hα' hlb' hα'γ).2.2, Subgroup.mem_bot] at h3
    have := h3
    rw [commutatorElement_def] at this
    calc q * r = (q * r * q⁻¹ * r⁻¹) * (r * q) := by group
      _ = r * q := by rw [this, one_mul]
  have hcQ : Qv γ ≤ Subgroup.centralizer ({r} : Set G) := by
    rw [← hsup]
    refine sup_le (fun q hq => ?_) (fun q hq => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hca q hq).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hcb q hq).symm
  obtain ⟨q, hqγ, hqla⟩ := IsConcreteLE.not_le_iff_exists.mp (Q_not_le hS hγ hla)
  have hqr : q * r = r * q := by
    have := Subgroup.mem_centralizer_iff.mp (hcQ hqγ) r rfl
    exact this.symm
  have hqs : q ∈ stab γ := S35.Ch.Qv_le_stab' γ hqγ
  have hqsl : q ∈ stab la := Qv_le_stab hS hla hqγ
  obtain ⟨β'', hβ''l, hβ''β, hβ''γ, hall⟩ := nbrs_S3_third hS vla hβ hla' hβγ
  let g : ↥(H ⊔ M) := ⟨q, stab_le γ hqs⟩
  have hgb : g • β ∈ nbrs la := smul_mem_nbrs_of_stab (g := g) hqsl hβ
  have hgγ : g • γ = γ := smul_eq_of_mem_stab (g := g) hqs
  have hgβ : g • β = β'' := by
    rcases hall _ hgb with h | h | h
    · exfalso
      exact hqla (mem_Qv_of_fix_two hS vla hβ hla' hβγ hqsl (mem_stab_of_smul_eq h) hqs)
    · exfalso
      rw [← hgγ] at h
      exact hβγ (MulAction.injective g h)
    · exact h
  have hrV : r ∈ Vn β'' := by
    have h1 : r ∈ Vn (g • β) := by
      rw [Vn_smul, mem_conjSub]
      have : q⁻¹ * r * q = r := by
        calc q⁻¹ * r * q = q⁻¹ * (r * q) := by group
          _ = q⁻¹ * (q * r) := by rw [hqr]
          _ = r := by group
      rw [this]
      exact (Subgroup.mem_inf.mp hr).1
    rwa [hgβ] at h1
  have := hII β la β'' vβ hβ' (mem_nbrs_symm.mp hβ''l) hβ''β
  have hrVβ : r ∈ Vn β := (Subgroup.mem_inf.mp hr).1
  exact hrla (this ▸ (Subgroup.mem_inf.mpr ⟨hrVβ, hrV⟩))

end S35.TB4

end F53.Stellmacher

end CFSG.Quasithin
