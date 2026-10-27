module

public import CFSG.Quasithin.MS93.S45RB
public import CFSG.Quasithin.MS93.S45RC
public import CFSG.Quasithin.MS93.S45RD

public section

namespace CFSG.Quasithin.MS93.S45R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S45
open scoped commutatorElement

theorem inv_mul_conj_mem_of_commutator_le {𝔾 : Type} [Group 𝔾] {C K W : Subgroup 𝔾}
    (hCK : ⁅C, K⁆ ≤ W) (k : ↥K) {x : 𝔾} (hx : x ∈ C) : x⁻¹ * ((k : 𝔾) * x * (k : 𝔾)⁻¹) ∈ W := by
  have hm := hCK (Subgroup.commutator_mem_commutator (C.inv_mem hx) k.2)
  simpa only [commutatorElement_def, inv_inv, mul_assoc] using hm

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem not_frattiniIn_le_of_deep (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {k : ℕ} (hk : Even k)
    (hkN : k + 120 ≤ N) :
    ¬ frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p (k + 60)), Ltil c.hyp.le L (p (k + 60))⁆ ≤
      Uloc c.hyp.le L (p (k + 60)) ⊔ Hloc c.hyp.le L (p (k + 60)) := by
  have h := c.hyp
  have ha : Even (k + 60) := hk.add (by decide)
  have hα := c.isMVtx_of_isGoodPath hp (k := k + 60) (by omega) ha
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hα
  obtain ⟨dual, hd⟩ := c.exists_isSum_vhat hα hψs hψ
  obtain rfl : dual = true := c.dual_eq_true hp (x := k + 54) (hk.add (by decide)) (by omega)
    (by omega) hψs hψ (c.isSum_bloc hα hd)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := top_data c h14 hSQ hZV hp ha (by omega)
    (by omega) (α := p (k + 60)) (γ := p (k + 62)) (μ := p (k + 64)) (ν := p (k + 66)) rfl rfl
    rfl rfl hψs hψ
  have hr := c.isGoodPath_rev hp (m := k + 100) (hk.add (by decide)) (by omega) (by omega)
  have hrv : ∀ i j, k + 100 - i = j → (fun i => p (k + 100 - i)) i = p j := fun i j hij => by
    simp only [hij]
  obtain ⟨r1, r2, r3, r4, r5, -, r7, -, -, -⟩ := top_data c h14 hSQ hZV hr (a := 40) (by decide)
    (by omega) (by omega) (α := p (k + 60)) (γ := p (k + 58)) (μ := p (k + 56))
    (ν := p (k + 54)) (hrv _ _ (by omega)) (hrv _ _ (by omega)) (hrv _ _ (by omega))
    (hrv _ _ (by omega)) hψs hψ
  have hW : whv c.hyp (p (k + 60)) (p (k + 58)) = whv c.hyp (p (k + 60)) (p (k + 62)) := by
    have e := c.whv_eq_of_isGoodPath hp (a := k + 60) ha (by omega) (by omega)
    rw [show k + 60 - 2 = k + 58 by omega] at e
    exact e.symm
  obtain ⟨g, hg, hgx⟩ := hp.straight (k + 60) ha (by omega) (by omega)
  have hgx' : g • p (k + 62) = p (k + 58) := by
    rw [show k + 60 - 2 = k + 58 by omega] at hgx
    exact hgx
  have hD : conjCl (stab (puAmalgam h.le) (p (k + 60))) (whv c.hyp (p (k + 58)) (p (k + 60))) =
      conjCl (stab (puAmalgam h.le) (p (k + 60))) (whv c.hyp (p (k + 62)) (p (k + 60))) := by
    rw [← hgx']
    exact vsix_eq_of_smul c hg
  rw [hW, hD] at r1
  rw [hW] at r2 r3 r4 r5 r7
  obtain ⟨-, C, -, -, hCs, hXC, -, -⟩ := h4
  obtain ⟨-, Cr, -, -, hCrs, hXCr, -, -⟩ := r4
  have hXC' := (sup_comm _ _).trans hXC
  have hXCr' := (sup_comm _ _).trans hXCr
  have hCs' := hCs.trans (sup_le h2 le_rfl)
  have hCrs' := hCrs.trans (sup_le r2 le_rfl)
  have hQK : Qv (puAmalgam h.le) (p (k + 60)) ≤ stab _ (p (k + 60)) := qv_le_stab _ _
  have hker := c.ker_toSL3_eq hα hψ
  have hQ1 : ∀ x (hx : x ∈ Qv (puAmalgam h.le) (p (k + 60))), toSL3 ψ ⟨x, hQK hx⟩ = 1 :=
    fun x hx => MonoidHom.mem_ker.mp (by rw [hker, Subgroup.mem_subgroupOf]; exact hx)
  obtain ⟨z, hz, y, hy, hzy⟩ := exists_commutator_not_mem_vhat c h14 hSQ hZV hp (d := k + 62)
    (hk.add (by decide)) (by omega) (by omega)
  rw [show k + 62 - 8 = k + 54 by omega] at hy
  have hZα : ZM (puAmalgam h.le) (p (k + 60)) ≤
      Vcirc h.le L (p (k + 62)) ⊔ ZM _ (p (k + 62)) := by
    have := c.zm_le_vhat_left' hZV hp (a := k + 62) (hk.add (by decide)) (by omega) (by omega)
    rwa [show k + 62 - 2 = k + 60 by omega] at this
  obtain ⟨v₁, hv₁, v₂, hv₂, hv⟩ := exists_commutator_not_mem_of_pairing hψs (NatSec.ofIsSum hd)
    (NatSec.ofIsSum h3) (NatSec.ofIsSum r3) hQK hQ1 h9 h8 h10 (le_sup_right.trans h1)
    (hXC'.le.trans h1) (hXCr'.le.trans r1) h6
    (fun s _ hx => inv_mul_conj_mem_of_commutator_le hCs' s hx)
    (fun s _ hx => inv_mul_conj_mem_of_commutator_le hCrs' s hx) h5 r5
    (S4A.le_normalizer_conjCl _ _) (hXC'.ge (h7 hz)) (hXCr'.ge (r7 hy))
    (fun hm => hzy (hZα hm))
  intro hle
  obtain ⟨hVp, hVf⟩ := c.isPGroup_commutator_qv_ltil hα
  have hUH : Uloc h.le L (p (k + 60)) ⊔ Hloc h.le L (p (k + 60)) ≤ ZM _ (p (k + 60)) :=
    sup_le (uloc_le_zm h c.full hα) ((Subgroup.commutator_mono (c.vcirc_le_vv _) le_rfl).trans
      ((c.commutator_vv_qv_le_zloc hα).trans (zloc_le_zm h c.full hα)))
  exact hv (hUH (hle (S45.commutator_le_frattiniIn hVp
    (Subgroup.commutator_mem_commutator hv₁ hv₂))))

theorem not_frattiniIn_le (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h34 : 34 ≤ a) (haN : a + 30 ≤ N) :
    ¬ frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ≤
      Uloc c.hyp.le L (p a) ⊔ Hloc c.hyp.le L (p a) := by
  obtain ⟨q, Nq, b, hq, hb, h60, hbN, -, hqb⟩ := exists_deep_isGoodPath c hp ha h34 haN 60
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 60 := ⟨b - 60, by omega⟩
  have hk : Even k := by
    obtain ⟨u, hu⟩ := hb
    exact ⟨u - 30, by omega⟩
  have := not_frattiniIn_le_of_deep c h14 hSQ hZV hq hk (by omega)
  rwa [hqb] at this

end Ctx

end CFSG.Quasithin.MS93.S45R
