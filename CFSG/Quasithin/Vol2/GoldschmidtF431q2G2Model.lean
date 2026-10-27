module

public import CFSG.Quasithin.Vol2.GoldschmidtF431q2G2Basic
public import CFSG.Quasithin.Vol2.GoldschmidtF431q2Loc
public import CFSG.Quasithin.Vol2.GoldschmidtF431q2G2Chk

public section

namespace CFSG.Quasithin.H13.F431.G2Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F6 CFSG.Quasithin.F6.G22Perm
  CFSG.Quasithin.F6.G22Shape CFSG.Sporadic.Bridge

namespace Model

variable {k : Type} [Field k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1)

include hk2

@[expose] noncomputable def TpSub : Subgroup (G2Group k) :=
  idxSub h2 hk2 (List.range 32) Tab.range32_lt (by decide) Tab.Tp_mul Tab.Tp_inv

@[expose] noncomputable def R2TpSub : Subgroup (G2Group k) :=
  idxSub h2 hk2 Tab.R2TpIdx Tab.R2Tp_lt (by decide) Tab.R2Tp_mul Tab.R2Tp_inv

theorem mem_TpSub {g : G2Group k} : g ∈ TpSub h2 hk2 ↔ ∃ i < 32, g = sEl h2 i := by
  simp [TpSub, mem_idxSub]

theorem sEl_mem_TpSub {i : ℕ} (hi : i < 32) : sEl h2 i ∈ TpSub h2 hk2 :=
  (mem_TpSub h2 hk2).2 ⟨i, hi, rfl⟩

theorem TpSub_le_S : TpSub h2 hk2 ≤ (lat h2 hk2).S := fun _ hg => by
  obtain ⟨i, hi, rfl⟩ := (mem_TpSub h2 hk2).1 hg
  exact sEl_mem_S h2 hk2 (by omega)

theorem card_TpSub : Nat.card (TpSub h2 hk2) = 32 := by
  rw [TpSub, card_idxSub h2 hk2 (List.nodup_range), List.length_range]

theorem sEl_eq_iff {i j : ℕ} (hi : i < 64) (hj : j < 64) : sEl h2 i = sEl h2 j ↔ i = j :=
  ⟨sEl_injective h2 hk2 hi hj, fun h => h ▸ rfl⟩

theorem sEl_conj {a j : ℕ} (ha : a < 64) (hj : j < 64) :
    sEl h2 a * sEl h2 j * (sEl h2 a)⁻¹ = sEl h2 (Tab.mulT (Tab.mulT a j) (Tab.invT a)) := by
  have h1 := (Tab.mulT_spec a ha j hj).1
  rw [sEl_inv h2 hk2 ha, sEl_mulT h2 hk2 ha hj, sEl_mulT h2 hk2 h1 (Tab.invT_spec a ha).1]

theorem zs_lift {w : G2Group k} (hw : w ∈ (lat h2 hk2).S)
    (hc : ∀ t ∈ (lat h2 hk2).S, t * w = w * t) : w = 1 ∨ w = sEl h2 26 := by
  obtain ⟨i, hi, rfl⟩ := (mem_S_iff h2 hk2).1 hw
  rcases Tab.ZS_chk i hi (fun j hj => by
    have := hc (sEl h2 j) (sEl_mem_S h2 hk2 hj)
    rw [sEl_mulT h2 hk2 hj hi, sEl_mulT h2 hk2 hi hj,
      sEl_eq_iff h2 hk2 (Tab.mulT_spec j hj i hi).1 (Tab.mulT_spec i hi j hj).1] at this
    exact this.symm) with h | h
  · exact Or.inl (h ▸ sEl_zero h2 hk2)
  · exact Or.inr (h ▸ rfl)

theorem sEl_sq {i : ℕ} (hi : i < 64) : sEl h2 i * sEl h2 i = 1 ↔ Tab.mulT i i = 0 := by
  rw [sEl_mulT h2 hk2 hi hi, ← sEl_zero h2 hk2,
    sEl_eq_iff h2 hk2 (Tab.mulT_spec i hi i hi).1 (by norm_num)]

theorem mem_R2 {g : G2Group k} : g ∈ R2 h2 hk2 ↔ ∃ i ∈ g22R2Idx, g = sEl h2 i := by
  simp [R2, mem_idxSub]

theorem mem_R2TpSub_iff {g : G2Group k} (hg : g ∈ R2 h2 hk2) :
    g ∈ TpSub h2 hk2 ↔ g ∈ R2TpSub h2 hk2 := by
  obtain ⟨i, hi, rfl⟩ := (mem_R2 h2 hk2).1 hg
  have hi64 := g22_R2_lt_chk i hi
  constructor
  · intro h
    obtain ⟨j, hj, e⟩ := (mem_TpSub h2 hk2).1 h
    have hij := (sEl_eq_iff h2 hk2 hi64 (by omega)).1 e
    exact ⟨i, Tab.R2Tp_of_lt i hi (by rw [hij]; exact hj), rfl⟩
  · rintro ⟨j, hj, e⟩
    have hij := (sEl_eq_iff h2 hk2 hi64 (Tab.R2Tp_lt j hj)).1 e
    exact sEl_mem_TpSub h2 hk2 (by rw [hij]; exact (Tab.R2Tp_mem j hj).2)

theorem isSylowTwoOf_S : IsSylowTwoOf (lat h2 hk2).S (lat h2 hk2).P₂ := by
  have e : ((lat h2 hk2).S.subgroupOf ⊤).index = (lat h2 hk2).S.index :=
    Subgroup.relIndex_top_right _
  exact F7.isSylowTwoOf_mono_right ⟨le_top, (lat h2 hk2).sylow.1, by rw [e]; exact
    (lat h2 hk2).sylow.2⟩ (lat h2 hk2).S_le_P₂ le_top

theorem g2Loc : G2Loc (lat h2 hk2).P₂ (sEl h2 26) (lat h2 hk2).S (R2 h2 hk2) (TpSub h2 hk2) := by
  have hR2n : ∀ h ∈ (lat h2 hk2).P₂, ∀ q ∈ R2 h2 hk2, h * q * h⁻¹ ∈ R2 h2 hk2 := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.1 (P₂_le_normalizer h2 hk2 g22_R2_lt_chk (fun _ => Iff.rfl)
      g22_R2_norm_chk hh) q).1 hq
  have hout : ∀ v ∈ R2 h2 hk2, v ∉ TpSub h2 hk2 → v * v = 1 →
      ∃ i ∈ g22R2Idx, v = sEl h2 i ∧ 32 ≤ i ∧ Tab.mulT i i = 0 := by
    intro v hv hvT hv2
    obtain ⟨i, hi, rfl⟩ := (mem_R2 h2 hk2).1 hv
    exact ⟨i, hi, rfl, by_contra fun h => hvT (sEl_mem_TpSub h2 hk2 (by omega)),
      (sEl_sq h2 hk2 (g22_R2_lt_chk i hi)).1 hv2⟩
  refine
    { z_ne := fun h => sEl_ne h2 hk2 (by norm_num) (by norm_num) (by norm_num)
        (h.trans (sEl_zero h2 hk2).symm)
      z_sq := (sEl_sq h2 hk2 (by norm_num)).2 Tab.zz_chk
      T_syl := isSylowTwoOf_S h2 hk2
      T_card := card_S h2 hk2
      T_Z := fun w hw hc => zs_lift h2 hk2 hw hc
      T_N := fun h hh h1 h2' => ?_
      Q_le := R2_le_S h2 hk2
      Q_card := card_R2 h2 hk2
      Q_norm := hR2n
      Q_comm := ?_
      Q_Z := ?_
      Q_nonab := ?_
      Tp_le := TpSub_le_S h2 hk2
      Tp_card := by rw [card_S, card_TpSub]
      z_mem := sEl_mem_TpSub h2 hk2 (by norm_num)
      Tp_norm := fun h hh q hq => ?_
      out_ex := ?_
      out_pair := ?_
      out_t := ?_ }
  · refine (lat h2 hk2).normS (Subgroup.mem_normalizer_iff.2 fun n => ⟨h1 n, fun hn => ?_⟩)
    have := h2' _ hn
    rwa [show h⁻¹ * (h * n * h⁻¹) * h = n by group] at this
  · rintro x hx y hy
    obtain ⟨i, hi, rfl⟩ := (mem_R2 h2 hk2).1 hx
    obtain ⟨j, hj, rfl⟩ := (mem_R2 h2 hk2).1 hy
    rw [sEl_comm h2 hk2 (g22_R2_lt_chk i hi) (g22_R2_lt_chk j hj)]
    rcases Tab.R2_comm_chk i hi j hj with h | h
    · exact Or.inl (h ▸ sEl_zero h2 hk2)
    · exact Or.inr (h ▸ rfl)
  · intro w hw hc
    obtain ⟨i, hi, rfl⟩ := (mem_R2 h2 hk2).1 hw
    rcases Tab.R2_Z_chk i hi (fun j hj => by
      have := hc (sEl h2 j) ((mem_R2 h2 hk2).2 ⟨j, hj, rfl⟩)
      have hi' := g22_R2_lt_chk i hi
      have hj' := g22_R2_lt_chk j hj
      rw [sEl_mulT h2 hk2 hj' hi', sEl_mulT h2 hk2 hi' hj',
        sEl_eq_iff h2 hk2 (Tab.mulT_spec j hj' i hi').1 (Tab.mulT_spec i hi' j hj').1] at this
      exact this.symm) with h | h
    · exact Or.inl (h ▸ sEl_zero h2 hk2)
    · exact Or.inr (h ▸ rfl)
  · obtain ⟨i, hi, j, hj, hne⟩ := Tab.R2_nonab_chk
    refine ⟨sEl h2 i, (mem_R2 h2 hk2).2 ⟨i, hi, rfl⟩, sEl h2 j, (mem_R2 h2 hk2).2 ⟨j, hj, rfl⟩,
      fun h => hne ?_⟩
    have hi' := g22_R2_lt_chk i hi
    have hj' := g22_R2_lt_chk j hj
    rw [sEl_mulT h2 hk2 hi' hj', sEl_mulT h2 hk2 hj' hi',
      sEl_eq_iff h2 hk2 (Tab.mulT_spec i hi' j hj').1 (Tab.mulT_spec j hj' i hi').1] at h
    exact h
  · have hN := P₂_le_normalizer (H := R2TpSub h2 hk2) h2 hk2 Tab.R2Tp_lt (fun _ => Iff.rfl)
      Tab.R2Tp_norm hh
    rw [mem_R2TpSub_iff h2 hk2 hq, mem_R2TpSub_iff h2 hk2 (hR2n h hh q hq)]
    exact Subgroup.mem_normalizer_iff.1 hN q
  · obtain ⟨i, hi, hi32, hii⟩ := Tab.out_ex_chk
    refine ⟨sEl h2 i, (mem_R2 h2 hk2).2 ⟨i, hi, rfl⟩, fun h => ?_,
      (sEl_sq h2 hk2 (g22_R2_lt_chk i hi)).2 hii⟩
    obtain ⟨j, hj, e⟩ := (mem_TpSub h2 hk2).1 h
    have := (sEl_eq_iff h2 hk2 (g22_R2_lt_chk i hi) (by omega)).1 e
    omega
  · intro v hv hvT hv2
    obtain ⟨i, hi, rfl, hi32, hii⟩ := hout v hv hvT hv2
    obtain ⟨a, ha, b, hb, hai, hbi, hab⟩ := Tab.out_pair_chk i hi hi32 hii
    have hi' := g22_R2_lt_chk i hi
    have ha' := g22_R2_lt_chk a ha
    have hb' := g22_R2_lt_chk b hb
    refine ⟨sEl h2 a, (mem_R2 h2 hk2).2 ⟨a, ha, rfl⟩, sEl h2 b, (mem_R2 h2 hk2).2 ⟨b, hb, rfl⟩,
      ?_, ?_, ?_⟩
    · rw [sEl_mulT h2 hk2 ha' hi', sEl_mulT h2 hk2 hi' ha', hai]
    · rw [sEl_mulT h2 hk2 hb' hi', sEl_mulT h2 hk2 hi' hb', hbi]
    · rw [sEl_comm h2 hk2 ha' hb', hab]
  · intro v hv hvT hv2
    obtain ⟨i, hi, rfl, hi32, hii⟩ := hout v hv hvT hv2
    obtain ⟨h1, h2'⟩ := Tab.out_t_chk i hi hi32 hii
    have hi' := g22_R2_lt_chk i hi
    have hc := Tab.commT_lt 1 (by norm_num) i hi'
    refine ⟨sEl h2 1, sEl_mem_S h2 hk2 (by norm_num), ?_, ?_⟩ <;>
      rw [sEl_comm h2 hk2 (i := 1) (by norm_num) hi'] <;> intro h
    · exact h1 ((sEl_eq_iff h2 hk2 hc (by norm_num)).1 (h.trans (sEl_zero h2 hk2).symm))
    · exact h2' ((sEl_eq_iff h2 hk2 hc (by norm_num)).1 h)

end Model

end CFSG.Quasithin.H13.F431.G2Two
