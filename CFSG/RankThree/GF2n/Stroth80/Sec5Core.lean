module

public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
theorem sec51_comm_mem {N : Subgroup G} {s x : G} (hs : s ∈ N) (hx : x ∈ N) : ⁅s, x⁆ ∈ N := by
  rw [commutatorElement_def]
  exact N.mul_mem (N.mul_mem (N.mul_mem hs hx) (N.inv_mem hs)) (N.inv_mem hx)

omit [Finite G] in
theorem sec51_comm_mem_inf {N P : Subgroup G} {l n : G} (hl : l ∈ P) (hn : n ∈ N)
    (hlN : l * n * l⁻¹ ∈ N) (hNP : ∀ n ∈ N, ∀ x ∈ P, n * x * n⁻¹ ∈ P) : ⁅l, n⁆ ∈ P ⊓ N := by
  refine ⟨?_, ?_⟩
  · have e : ⁅l, n⁆ = l * (n * l⁻¹ * n⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact P.mul_mem hl (hNP n hn _ (P.inv_mem hl))
  · have e : ⁅l, n⁆ = (l * n * l⁻¹) * n⁻¹ := commutatorElement_def l n
    rw [e]
    exact N.mul_mem hlN (N.inv_mem hn)

theorem sec51_exists_subgroup (N D : Subgroup G) (hDN : D ≤ N) :
    ∃ S : Subgroup G, ∀ s, s ∈ S ↔ ∀ x ∈ N, ⁅s, x⁆ ∈ D := by
  have hnorm : ∀ s : G, (∀ x ∈ N, ⁅s, x⁆ ∈ D) → s ∈ Subgroup.normalizer (D : Set G) := by
    intro s hs
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have e : s * x * s⁻¹ = ⁅s, x⁆ * x := by simp only [commutatorElement_def]; group
    rw [e]
    exact D.mul_mem (hs x (hDN hx)) hx
  refine ⟨{ carrier := {s | ∀ x ∈ N, ⁅s, x⁆ ∈ D}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun s => Iff.rfl⟩
  · intro a b ha hb x hx
    have e : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact D.mul_mem ((Subgroup.mem_normalizer_iff.mp (hnorm a ha) _).mp (hb x hx)) (ha x hx)
  · intro x _
    simpa [commutatorElement_def] using D.one_mem
  · intro a ha x hx
    have e : ⁅a⁻¹, x⁆ = a⁻¹ * ⁅a, x⁆⁻¹ * a := by simp only [commutatorElement_def]; group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (D : Set G)).inv_mem (hnorm a ha)) _).mp (D.inv_mem (ha x hx))
    simpa using this

theorem sec51_abstract {R N L L' : Subgroup G} {r : G} (hr : r ∈ R)
    (hL' : L' = conjSubgroup r L) (hNnorm : ∀ s ∈ R, ∀ x ∈ N, s * x * s⁻¹ ∈ N)
    (hNL : ∀ n ∈ N, ∀ x ∈ L, n * x * n⁻¹ ∈ L) (hNL' : ∀ n ∈ N, ∀ x ∈ L', n * x * n⁻¹ ∈ L')
    (hN : N = ⨆ (h : G) (_ : h ∈ R), conjSubgroup h L ⊓ N) (hNN : ⁅N, N⁆ ≤ L)
    (hgen : R = N ⊔ L ⊔ L') :
    (∀ x ∈ N, ∃ a ∈ L ⊓ N, ∃ b ∈ L' ⊓ N, x = a * b) ∧ ⁅N, N⁆ ≤ L ⊓ L' := by
  have hNR : N ≤ R := by rw [hgen]; exact le_sup_left.trans le_sup_left
  have hLR : L ≤ R := by rw [hgen]; exact le_sup_right.trans le_sup_left
  have hL'R : L' ≤ R := by rw [hgen]; exact le_sup_right
  have hcL : ∀ l ∈ L, ∀ n ∈ N, ⁅l, n⁆ ∈ L ⊓ N := fun l hl n hn =>
    sec51_comm_mem_inf hl hn (hNnorm l (hLR hl) n hn) hNL
  have hcL' : ∀ l ∈ L', ∀ n ∈ N, ⁅l, n⁆ ∈ L' ⊓ N := fun l hl n hn =>
    sec51_comm_mem_inf hl hn (hNnorm l (hL'R hl) n hn) hNL'
  have hDN : (L ⊓ N) ⊔ (L' ⊓ N) ≤ N := sup_le inf_le_right inf_le_right
  have hAD : L ⊓ N ≤ (L ⊓ N) ⊔ (L' ⊓ N) := le_sup_left
  have hA'D : L' ⊓ N ≤ (L ⊓ N) ⊔ (L' ⊓ N) := le_sup_right
  obtain ⟨S, hS⟩ := sec51_exists_subgroup N ((L ⊓ N) ⊔ (L' ⊓ N)) hDN
  have hNS : N ≤ S := fun s hs => (hS s).mpr fun x hx =>
    hAD ⟨hNN (Subgroup.commutator_mem_commutator hs hx), sec51_comm_mem hs hx⟩
  have hLS : L ≤ S := fun s hs => (hS s).mpr fun x hx => hAD (hcL s hs x hx)
  have hL'S : L' ≤ S := fun s hs => (hS s).mpr fun x hx => hA'D (hcL' s hs x hx)
  have hRS : R ≤ S := by rw [hgen]; exact sup_le (sup_le hNS hLS) hL'S
  have hRD : ∀ s ∈ R, ∀ x ∈ N, ⁅s, x⁆ ∈ (L ⊓ N) ⊔ (L' ⊓ N) := fun s hs => (hS s).mp (hRS hs)
  have hND : N ≤ (L ⊓ N) ⊔ (L' ⊓ N) := by
    refine hN.le.trans (iSup₂_le fun h hh y hy => ?_)
    have hyL : h⁻¹ * y * h ∈ L := mem_conjSubgroup.mp hy.1
    have hyN : h⁻¹ * y * h ∈ N := by simpa using hNnorm h⁻¹ (R.inv_mem hh) y hy.2
    have e : y = ⁅h, h⁻¹ * y * h⁆ * (h⁻¹ * y * h) := by simp only [commutatorElement_def]; group
    rw [e]
    exact ((L ⊓ N) ⊔ (L' ⊓ N)).mul_mem (hRD h hh _ hyN) (hAD ⟨hyL, hyN⟩)
  have hAnorm : L ⊓ N ≤ Subgroup.normalizer ((L' ⊓ N : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    exact ⟨hNL' a ha.2 b hb.1, N.mul_mem (N.mul_mem ha.2 hb.2) (N.inv_mem ha.2)⟩
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_normalizer hAnorm (hND hx)
    exact ⟨a, ha, b, hb, hab.symm⟩
  · refine le_inf hNN (Subgroup.commutator_le.mpr fun a ha b hb => ?_)
    rw [hL', mem_conjSubgroup]
    have e : r⁻¹ * ⁅a, b⁆ * r = ⁅r⁻¹ * a * r, r⁻¹ * b * r⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 : r⁻¹ * a * r ∈ N := by simpa using hNnorm r⁻¹ (R.inv_mem hr) a ha
    have h2 : r⁻¹ * b * r ∈ N := by simpa using hNnorm r⁻¹ (R.inv_mem hr) b hb
    exact hNN (Subgroup.commutator_mem_commutator h1 h2)

theorem Ctx.CN_conj_mem (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {s x : G}
    (hs : s ∈ Rt M (LB M Q B) t) (hx : x ∈ hc.CN t) : s * x * s⁻¹ ∈ hc.CN t := by
  obtain ⟨hxR, hxV⟩ := Ctx.mem_CN.mp hx
  refine Ctx.mem_CN.mpr ⟨(Rt M (LB M Q B) t).mul_mem
    ((Rt M (LB M Q B) t).mul_mem hs hxR) ((Rt M (LB M Q B) t).inv_mem hs), fun v hv => ?_⟩
  have hsM : s ∈ M := hc.Rt_le_M t hs
  have hv' : s⁻¹ * v * s ∈ Vt M (LB M Q B) B Z t := by
    have := (Subgroup.mem_normalizer_iff.mp
      (hc.Rt_normalizes_Vt ht ((Rt M (LB M Q B) t).inv_mem hs)) v).mp hv
    simpa using this
  have e : ⁅s * x * s⁻¹, v⁆ = s * ⁅x, s⁻¹ * v * s⁆ * s⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hsM) _).mp (hxV _ hv')

theorem Ctx.CN_normalizes_conj_LB (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {t : G} (ht : t ∈ LB M Q B)
    {h : G} (hh : h ∈ Rt M (LB M Q B) t) {n : G} (hn : n ∈ hc.CN t) :
    n ∈ Subgroup.normalizer (conjSubgroup h (LB M Q B) : Set G) := by
  obtain ⟨hnR, hnV⟩ := Ctx.mem_CN.mp hn
  have hhM : h ∈ M := hc.Rt_le_M t hh
  have hnM : n ∈ M := hc.Rt_le_M t hnR
  have hT : t ∈ conjSubgroup h (LB M Q B) := by
    rw [mem_conjSubgroup]
    have e : h⁻¹ * t * h = ⁅h⁻¹, t⁆ * t := by simp only [commutatorElement_def]; group
    rw [e]
    exact (LB M Q B).mul_mem
      (sec39_Q_le_LB (hc.Rt_comm_mem_Q ((Rt M (LB M Q B) t).inv_mem hh))) ht
  rw [← hc.LB_conj hhM, (hc.conj_of_mem hhM).mem_normalizer_LB_iff (hc.CQt_conj hhM h35) hnM]
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hxV : x ∈ Vt M (LB M Q B) B Z t :=
    (sup_le (sec39_conjB_le_Vt hhM hT) sec39_Z_le_Vt : conjSubgroup h B ⊔ Z ≤ _) hx
  have e : n * x * n⁻¹ = ⁅n, x⁆ * x := by simp only [commutatorElement_def]; group
  rw [e]
  exact (conjSubgroup h B ⊔ Z : Subgroup G).mul_mem (Subgroup.mem_sup_right (hnV x hxV)) hx

theorem Ctx.sec51_core (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G))
    {t : G} (ht : t ∈ LB M Q B) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hN : hc.CN t = ⨆ (h : G) (_ : h ∈ Rt M (LB M Q B) t),
      conjSubgroup h (LB M Q B) ⊓ hc.CN t)
    (hNN : ⁅hc.CN t, hc.CN t⁆ ≤ LB M Q B)
    (hgen : Rt M (LB M Q B) t = hc.CN t ⊔ LB M Q B ⊔ LB M Q (conjSubgroup r B)) :
    (∀ x ∈ hc.CN t, ∃ a ∈ LB M Q B ⊓ hc.CN t,
        ∃ b ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, x = a * b) ∧
    (∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B), ⁅s, x⁆ ∈ Q) ∧
    ⁅hc.CN t, hc.CN t⁆ ≤ LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hL' : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) := hc.LB_conj hrM
  have hcr := hc.conj_of_mem hrM
  have hNL : ∀ n ∈ hc.CN t, ∀ x ∈ LB M Q B, n * x * n⁻¹ ∈ LB M Q B := by
    intro n hn x hx
    have h1 := hc.CN_normalizes_conj_LB h35 ht (Rt M (LB M Q B) t).one_mem hn
    rw [conjSubgroup_one] at h1
    exact (Subgroup.mem_normalizer_iff.mp h1 x).mp hx
  have hNL' : ∀ n ∈ hc.CN t, ∀ x ∈ LB M Q (conjSubgroup r B),
      n * x * n⁻¹ ∈ LB M Q (conjSubgroup r B) := by
    intro n hn x hx
    have h1 := hc.CN_normalizes_conj_LB h35 ht hr hn
    rw [← hL'] at h1
    exact (Subgroup.mem_normalizer_iff.mp h1 x).mp hx
  obtain ⟨hprod, hcomm⟩ := sec51_abstract hr hL' (fun s hs x hx => hc.CN_conj_mem ht hs hx)
    hNL hNL' hN hNN hgen
  refine ⟨hprod, ?_, hcomm⟩
  intro s hs x hx
  have hLT : LB M Q B ≤ CommQ hc.hyp.Q_normal.2 x := fun l hl =>
    mem_CommQ.mpr ⟨hc.LB_le_M hl, Subgroup.commutator_le.mp hc.commutator_LB_le_Q l hl x hx.1⟩
  have hL'T : LB M Q (conjSubgroup r B) ≤ CommQ hc.hyp.Q_normal.2 x := fun l hl =>
    mem_CommQ.mpr ⟨hcr.LB_le_M hl,
      Subgroup.commutator_le.mp hcr.commutator_LB_le_Q l hl x hx.2⟩
  have hNT : hc.CN t ≤ CommQ hc.hyp.Q_normal.2 x := by
    intro n hn
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod n hn
    exact (CommQ hc.hyp.Q_normal.2 x).mul_mem (hLT ha.1) (hL'T hb.1)
  have hRT : Rt M (LB M Q B) t ≤ CommQ hc.hyp.Q_normal.2 x := by
    rw [hgen]
    exact sup_le (sup_le hNT hLT) hL'T
  exact (mem_CommQ.mp (hRT hs)).2

end CFSG.RankThree.GF2n.Stroth80
