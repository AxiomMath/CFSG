module

public import Certificates.Certificate1322008
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofON

public noncomputable section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.ONSchreier CFSG.ONSchreier.Native Subgroup
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14.Ronan148D

attribute [local irreducible] dotProduct

@[expose] def seedG (j m : ℕ) : GM :=
  (nL j (m / 2))⁻¹ * (if m % 2 = 0 then k1G else k2G) * nL j (m / 2)

theorem e27InitG_seed {j : ℕ}
    (hj : j < 2) {m : ℕ} (hm : m < 8) : (e27InitG j).getD m 1 = (seedG j m).1 := by
  rw [e27InitG_getD j (by omega), if_pos hm]
  have hn := eM_rL hj (show m / 2 < 4 by omega)
  unfold e27NReg e27KReg
  rw [hn]
  simp only [seedG, Subgroup.coe_mul, Subgroup.coe_inv]
  split_ifs <;> rfl

theorem wordG_mem {X : Type*} [Group X] {K : Subgroup X} {R : Array X} {w : List (ℕ × Bool)}
    (h : ∀ l ∈ w, R.getD l.1 1 ∈ K) : wordG R w ∈ K := by
  unfold wordG
  apply K.list_prod_mem
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  split
  · exact h l hl
  · exact K.inv_mem (h l hl)

theorem closure_centSeed
    {j : ℕ} (hj : j < 2) :
    Subgroup.closure (Set.range fun m : Fin 8 => seedG j m) = ⊤ := by
  set Kp : Subgroup Mat45ˣ :=
    (Subgroup.closure (Set.range fun m : Fin 8 => seedG j m)).map M.subtype with hKp
  have hgen : ∀ k : Fin 8, gM k ∈ Kp := by
    intro k
    rw [← Certificates.certificate1322008 j hj k]
    refine wordG_mem fun l hl => ?_
    have hl8 := centWord_lt j hj k k.isLt l hl
    rw [e27InitG_seed hj hl8]
    exact ⟨seedG j l.1, subset_closure ⟨⟨l.1, hl8⟩, rfl⟩, rfl⟩
  have hM : M ≤ Kp := by
    have hcl : M = Subgroup.closure (Set.range gM) := by
      rw [M, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
        ← Set.range_comp]
      have : (⇑psiM ∘ PresentedGroup.of) = gM := funext fun k => psiM_of k
      rw [this]
    rw [hcl, closure_le]
    rintro _ ⟨k, rfl⟩
    exact hgen k
  rw [eq_top_iff]
  intro g _
  obtain ⟨h, hh, he⟩ := hM g.2
  have : h = g := Subtype.ext he
  rw [← this]
  exact hh

theorem seedG_mem_centralizer
    (j m : ℕ) : seedG j m ∈ centralizer {mL j (m / 2)} := by
  have hk : (if m % 2 = 0 then k1G else k2G) ∈ K0G := by
    split_ifs
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
  have hc := K0_comm hk
  rw [mem_centralizer_singleton_iff]
  simp only [seedG, mL]
  calc (nL j (m / 2))⁻¹ * (if m % 2 = 0 then k1G else k2G) * nL j (m / 2) *
        ((nL j (m / 2))⁻¹ * xG 0 * nL j (m / 2))
      = (nL j (m / 2))⁻¹ * ((if m % 2 = 0 then k1G else k2G) * xG 0) * nL j (m / 2) := by group
    _ = (nL j (m / 2))⁻¹ * (xG 0 * (if m % 2 = 0 then k1G else k2G)) * nL j (m / 2) := by
        rw [hc]
    _ = (nL j (m / 2))⁻¹ * xG 0 * nL j (m / 2) *
        ((nL j (m / 2))⁻¹ * (if m % 2 = 0 then k1G else k2G) * nL j (m / 2)) := by group

theorem uL_ne_zero : ∀ j < 2, ∀ l < 4, uL j l ≠ 0 := by
  decide +kernel

theorem mL_not_mem_zpowers
    {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) :
    mL j l ∉ zpowers zG := fun h =>
  uL_ne_zero j hj l hl ((coord_mL hj hl).symm.trans
    ((relG.coord_eq_zero_iff ⟨mL j l, mL_mem_P0 hj hl⟩).2 h))

theorem iSup_centralizer_AG
    {j : ℕ} (hj : j < 2) :
    ⨆ (a : GM) (_ : a ∈ AG j) (_ : a ∉ zpowers zG), centralizer {a} = ⊤ := by
  rw [eq_top_iff, ← closure_centSeed hj, closure_le]
  rintro _ ⟨m, rfl⟩
  have hl : (m : ℕ) / 2 < 4 := by omega
  exact mem_iSup_of_mem (mL j ((m : ℕ) / 2)) (mem_iSup_of_mem (mL_mem_AG hj hl)
    (mem_iSup_of_mem (mL_not_mem_zpowers hj hl) (seedG_mem_centralizer j m)))

theorem isE27_sup_zpowers
    {F : Subgroup GM} (hF : CFSG.Open.IsElemAbelian 3 F)
    (hc : Nat.card F = 9) (hz : F ⊓ zpowers zG = ⊥) : Late.IsE27 (F ⊔ zpowers zG) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : CFSG.Open.IsElemAbelian 3 (zpowers zG) :=
    Sec4.Res417Five.isElemAbelian_zpowers_of_cube relG.xcube
  have hA : CFSG.Open.IsElemAbelian 3 (F ⊔ zpowers zG) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hF hZ fun a _ b hb => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      exact (Commute.zpow_left (zG_central a) k).symm.eq
  refine ⟨hA, le_antisymm ?_ ?_⟩
  · have hp : IsPGroup 3 ↥(F ⊔ zpowers zG) := fun g => ⟨1, by
      rw [pow_one]; exact Subtype.ext (by simpa using hA.2 g.1 g.2)⟩
    exact Sec4.Res417Five.card_le_27_of_abelian_model hp fun a ha b hb =>
      congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · have hp : IsPGroup 3 ↥(F ⊔ zpowers zG) := fun g => ⟨1, by
      rw [pow_one]; exact Subtype.ext (by simpa using hA.2 g.1 g.2)⟩
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hle : F < F ⊔ zpowers zG := by
      refine lt_of_le_of_ne le_sup_left fun h => ?_
      have hzF : zG ∈ F := h ▸ mem_sup_right (mem_zpowers zG)
      have : zG ∈ F ⊓ zpowers zG := ⟨hzF, mem_zpowers zG⟩
      rw [hz, mem_bot] at this
      exact relG.x1 this
    have hlt := card_lt_of_lt hle
    have hdvd := card_dvd_of_le (le_sup_left : F ≤ F ⊔ zpowers zG)
    rw [hc, hn] at hdvd
    rw [hc, hn] at hlt
    rw [hn]
    rcases (show n ≤ 2 ∨ 3 ≤ n by omega) with h2 | h3
    · interval_cases n <;> norm_num at hlt
    · calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h3

theorem iSup_centralizer_E9
    {F : Subgroup GM} (hF : CFSG.Open.IsElemAbelian 3 F)
    (hc : Nat.card F = 9) (hz : F ⊓ zpowers zG = ⊥) :
    ⨆ (f : GM) (_ : f ∈ F) (_ : f ≠ 1), centralizer {f} = ⊤ := by
  set T := ⨆ (f : GM) (_ : f ∈ F) (_ : f ≠ 1), centralizer {f} with hT
  have : (zpowers zG).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    rw [(Commute.zpow_left (zG_central g) k).symm.eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers zG) k⟩
  obtain ⟨h, j, hj, hAh⟩ := exists_conj_AG (isE27_sup_zpowers hF hc hz)
  have hzpow : ∀ c : ℤ, MulAut.conj h (zG ^ c) = zG ^ c := fun c => by
    rw [MulAut.conj_apply, (Commute.zpow_left (zG_central h) c).symm.eq, mul_inv_cancel_right]
  have hconj : ∀ x y : GM, y ∈ centralizer {h * x * h⁻¹} → h⁻¹ * y * h ∈ centralizer {x} := by
    intro x y hy
    rw [mem_centralizer_singleton_iff] at hy ⊢
    calc h⁻¹ * y * h * x = h⁻¹ * (y * (h * x * h⁻¹)) * h := by group
      _ = h⁻¹ * (h * x * h⁻¹ * y) * h := by rw [hy]
      _ = x * (h⁻¹ * y * h) := by group
  have hle : ⨆ (a : GM) (_ : a ∈ AG j) (_ : a ∉ zpowers zG), centralizer {a} ≤
      T.map (MulAut.conj h).toMonoidHom := by
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun haz => ?_
    rw [← hAh] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨f, hf, w, hw, rfl⟩ := mem_sup_of_normal_right.1 ha₀
    obtain ⟨c, rfl⟩ := mem_zpowers_iff.1 hw
    have e : (MulAut.conj h).toMonoidHom (f * zG ^ c) = h * f * h⁻¹ * zG ^ c := by
      rw [MulEquiv.coe_toMonoidHom, map_mul, hzpow, MulAut.conj_apply]
    rw [e] at haz ⊢
    have hf1 : f ≠ 1 := by
      rintro rfl
      apply haz
      rw [mul_one, mul_inv_cancel, one_mul]
      exact zpow_mem (mem_zpowers zG) c
    intro g hg
    have hg2 : g ∈ centralizer {h * f * h⁻¹} := by
      rw [mem_centralizer_singleton_iff] at hg ⊢
      have hzc : zG ^ c * g = g * zG ^ c := (Commute.zpow_left (zG_central g) c).eq
      apply mul_right_cancel (b := zG ^ c)
      calc g * (h * f * h⁻¹) * zG ^ c = g * (h * f * h⁻¹ * zG ^ c) := by group
        _ = h * f * h⁻¹ * zG ^ c * g := hg
        _ = h * f * h⁻¹ * (zG ^ c * g) := by group
        _ = h * f * h⁻¹ * (g * zG ^ c) := by rw [hzc]
        _ = h * f * h⁻¹ * g * zG ^ c := by group
    refine ⟨h⁻¹ * g * h,
      mem_iSup_of_mem f (mem_iSup_of_mem hf (mem_iSup_of_mem hf1 (hconj f g hg2))), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have htop : T.map (MulAut.conj h).toMonoidHom = ⊤ :=
    eq_top_iff.2 ((iSup_centralizer_AG hj).symm.le.trans hle)
  rw [eq_top_iff]
  intro g _
  have hg : MulAut.conj h g ∈ T.map (MulAut.conj h).toMonoidHom := by rw [htop]; trivial
  obtain ⟨g', hg', he⟩ := hg
  have : g' = g := (MulAut.conj h).injective he
  rw [← this]
  exact hg'

end CFSG.RankThree.Native.ONTriple
