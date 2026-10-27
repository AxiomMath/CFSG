module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Blk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Rk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Blocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

theorem s16h_z3_t_spec {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A L L₂ : Subgroup (MulAut W)} {x : MulAut W} (hB : s16h_Z3Blocks A L L₂ x)
    (hL : Nat.card ↥L = 3) (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥) {t : MulAut W} (htA : t ∈ A)
    (htr : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3)
    (htL : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥) :
    (∀ l ∈ L, t * l * t⁻¹ = l⁻¹) ∧ ∀ l ∈ L₂, t * l = l * t := by
  let U := commSub (⊤ : Subgroup W) L
  let U₂ := commSub (⊤ : Subgroup W) L₂
  have hUmap_of_not_norm : t ∉ normalizer (L : Set (MulAut W)) →
      U.map t.toMonoidHom = U₂ := by
    intro htn
    have hLmap : L.map (MulAut.conj t).toMonoidHom = L₂ := by
      rcases hB.perm t htA with h | h
      · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.1) htn
      · exact h.1
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact commSub_top_map151b (X := L) (Y := L₂) (g := t)
        (by
          intro x hx
          have := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom hx
          rwa [hLmap] at this
        ) u hu
    · intro c hc
      have hc' : t⁻¹ c ∈ U := by
        apply commSub_top_map151b (X := L₂) (Y := L) (g := t⁻¹)
        · intro x hx
          have hx' : x ∈ L.map (MulAut.conj t).toMonoidHom := by rwa [hLmap]
          obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
          rw [show (MulAut.conj t).toMonoidHom y = t * y * t⁻¹ from
            MulAut.conj_apply t y] at hyx
          have : t⁻¹ * (t * y * t⁻¹) * (t⁻¹)⁻¹ = y := by group
          rw [← hyx, this]
          exact hy
        · exact hc
      simpa using Subgroup.mem_map_of_mem t.toMonoidHom hc'
  have htN : t ∈ normalizer (L : Set (MulAut W)) := by
    by_contra htn
    have hUmap := hUmap_of_not_norm htn
    have hdis : U ⊓ U.map t.toMonoidHom = ⊥ := by rw [hUmap, hB.inf]
    have hle := s16h_bl_rk_le_of_inf_eq_bot hdis
    have hU6 : rk ↥U = 6 := hrk
    omega
  have hLmap : L.map (MulAut.conj t).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp htN
  have hL2map : L₂.map (MulAut.conj t).toMonoidHom = L₂ := by
    rcases hB.perm t htA with h | h
    · exact h.2
    · exfalso
      rw [h.1] at hLmap
      exact hB.ne hLmap
  have ht_inv : ∀ l ∈ L, t * l * t⁻¹ = l⁻¹ := by
    have := CFSG.Semidihedral.Principal.conj_eq_or_inv_of_mem_normalizer_of_card_three hL htN
    rcases this with hcent | hinv
    · exfalso
      apply htL
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk_comm : k * l = l * k := by
        have ht_comm_l : t * l = l * t := by
          calc t * l = (t * l * t⁻¹) * t := by group
            _ = l * t := by rw [hcent l hl]
        have hzl : Subgroup.zpowers t ≤ Subgroup.centralizer ({l} : Set (MulAut W)) := by
          rw [Subgroup.zpowers_le]
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact ht_comm_l.symm
        have hk' : l * k = k * l := by
          have := hzl hk
          rw [Subgroup.mem_centralizer_iff] at this
          exact this l (Set.mem_singleton l)
        exact hk'.symm
      exact hk_comm
    · exact hinv
  have ht_stabU : Subgroup.zpowers t ≤ stabSub U :=
    Subgroup.zpowers_le.mpr (hB.stab t htA hLmap).1
  have ht_stabU₂ : Subgroup.zpowers t ≤ stabSub U₂ :=
    Subgroup.zpowers_le.mpr (hB.stab t htA hLmap).2
  have h3 : 3 ≤ rk ↥(commSub U (Subgroup.zpowers t)) :=
    s16h_three_le_rk_of_inverts_Z3 hW hL hrk hfix ht_inv
  have h_inf : commSub U (Subgroup.zpowers t) ⊓ commSub U₂ (Subgroup.zpowers t) = ⊥ := by
    have hYU : commSub U (Subgroup.zpowers t) ≤ U := by
      apply commSub_le_of_invariant
      intro y hy w hw
      exact (mem_stabSub.mp (ht_stabU hy) w).2 hw
    have hYU₂ : commSub U₂ (Subgroup.zpowers t) ≤ U₂ := by
      apply commSub_le_of_invariant
      intro y hy w hw
      exact (mem_stabSub.mp (ht_stabU₂ hy) w).2 hw
    have hle : commSub U (Subgroup.zpowers t) ⊓ commSub U₂ (Subgroup.zpowers t) ≤ U ⊓ U₂ :=
      le_inf (inf_le_left.trans hYU) (inf_le_right.trans hYU₂)
    rw [hB.inf] at hle
    exact le_bot_iff.mp hle
  have h_le : commSub U (Subgroup.zpowers t) ⊔ commSub U₂ (Subgroup.zpowers t) ≤
      commSub (⊤ : Subgroup W) (Subgroup.zpowers t) :=
    sup_le (commSub_mono le_top le_rfl) (commSub_mono le_top le_rfl)
  have h_sum : rk ↥(commSub U (Subgroup.zpowers t)) +
      rk ↥(commSub U₂ (Subgroup.zpowers t)) ≤ 3 := by
    have hs := rk_sup_add_rk_inf (commSub U (Subgroup.zpowers t))
      (commSub U₂ (Subgroup.zpowers t))
    rw [h_inf, rk_bot, add_zero] at hs
    rw [← hs]
    exact le_trans (rk_mono h_le) htr
  have h_zero : rk ↥(commSub U₂ (Subgroup.zpowers t)) = 0 := by omega
  have h_bot : commSub U₂ (Subgroup.zpowers t) = ⊥ := (rk_eq_zero_iff hW).mp h_zero
  have h_fix : U₂ ≤ fixV (Subgroup.zpowers t) := commSub_eq_bot_iff.mp h_bot
  have ht_u₂ : ∀ u₂ ∈ U₂, t u₂ = u₂ := by
    intro u₂ hu₂
    exact mem_fixV_zpowers_iff_apply.mp (h_fix hu₂)
  refine ⟨ht_inv, ?_⟩
  intro l hl₂
  have hl_u : ∀ u ∈ U, l u = u := (mem_centSub.mp (hB.cent₂ hl₂))
  have h_conj : t * l * t⁻¹ = l := by
    ext w
    obtain ⟨u, hu, u₂, hu₂, rfl⟩ :=
      Subgroup.mem_sup.mp (by rw [hB.sup]; exact Subgroup.mem_top w)
    have htinv_u : t⁻¹ u ∈ U :=
      (mem_stabSub.mp (inv_mem (hB.stab t htA hLmap).1) u).2 hu
    have hl_tinv_u : l (t⁻¹ u) = t⁻¹ u := hl_u (t⁻¹ u) htinv_u
    have ht_u₂' : t u₂ = u₂ := ht_u₂ u₂ hu₂
    have htinv_u₂ : t⁻¹ u₂ = u₂ := by
      have := congrArg (fun x => t⁻¹ x) ht_u₂'
      rw [MulAut.inv_apply_self W t u₂] at this
      exact this.symm
    have hl_u₂_mem : l u₂ ∈ U₂ :=
      commSub_top_stable151b (X := L₂) (g := l)
        (by intro x hx; exact L₂.mul_mem (L₂.mul_mem hl₂ hx) (L₂.inv_mem hl₂)) u₂ hu₂
    have ht_l_u₂ : t (l u₂) = l u₂ := ht_u₂ (l u₂) hl_u₂_mem
    have hl_u' : l u = u := hl_u u hu
    simp only [MulAut.mul_apply, map_mul, htinv_u₂, hl_tinv_u, MulAut.apply_inv_self,
      ht_l_u₂, hl_u']
  rw [show t * l = (t * l * t⁻¹) * t by group, h_conj]

theorem s16h_z3_cent_block_of_commute {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A L L₂ : Subgroup (MulAut W)} {x : MulAut W}
    (hB : s16h_Z3Blocks A L L₂ x) (hL : Nat.card ↥L = 3)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥) {i : MulAut W}
    (hiL : ∀ l ∈ L, i * l = l * i) (hiL₂ : ∀ l ∈ L₂, i * l = l * i)
    (hri : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers i)) ≤ 2) :
    i ∈ centSub (commSub (⊤ : Subgroup W) L) ∨ i ∈ centSub (commSub (⊤ : Subgroup W) L₂) := by
  let U := commSub (⊤ : Subgroup W) L
  let U₂ := commSub (⊤ : Subgroup W) L₂
  let Y := commSub U (Subgroup.zpowers i)
  let Y₂ := commSub U₂ (Subgroup.zpowers i)
  have hi_normL : ∀ x ∈ L, i * x * i⁻¹ ∈ L := by
    intro x hx
    rw [hiL x hx]
    simpa using hx
  have hiinv_normL : ∀ x ∈ L, i⁻¹ * x * i ∈ L := by
    intro x hx
    have h1 : i * x * i⁻¹ = x := by
      rw [hiL x hx]
      group
    have h2 : i⁻¹ * x * i = x := by
      conv_lhs => rw [← h1]
      group
    rw [h2]
    exact hx
  have hi_stabU : i ∈ stabSub U := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have := commSub_top_stable151b hiinv_normL (i u) hu
      simpa using this
    · intro hu
      exact commSub_top_stable151b hi_normL u hu
  have hi_normL₂ : ∀ x ∈ L₂, i * x * i⁻¹ ∈ L₂ := by
    intro x hx
    rw [hiL₂ x hx]
    simpa using hx
  have hiinv_normL₂ : ∀ x ∈ L₂, i⁻¹ * x * i ∈ L₂ := by
    intro x hx
    have h1 : i * x * i⁻¹ = x := by
      rw [hiL₂ x hx]
      group
    have h2 : i⁻¹ * x * i = x := by
      conv_lhs => rw [← h1]
      group
    rw [h2]
    exact hx
  have hi_stabU₂ : i ∈ stabSub U₂ := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have := commSub_top_stable151b hiinv_normL₂ (i u) hu
      simpa using this
    · intro hu
      exact commSub_top_stable151b hi_normL₂ u hu
  have hzp_stabU : Subgroup.zpowers i ≤ stabSub U := Subgroup.zpowers_le.mpr hi_stabU
  have hzp_stabU₂ : Subgroup.zpowers i ≤ stabSub U₂ := Subgroup.zpowers_le.mpr hi_stabU₂
  have hY_le_U : Y ≤ U := by
    apply commSub_le_of_invariant
    intro x hx w hw
    exact (mem_stabSub.mp (hzp_stabU hx) w).2 hw
  have hY₂_le_U₂ : Y₂ ≤ U₂ := by
    apply commSub_le_of_invariant
    intro x hx w hw
    exact (mem_stabSub.mp (hzp_stabU₂ hx) w).2 hw
  have hY_inv : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y := by
    intro l hl y hy
    have hl_norm_i : ∀ x ∈ Subgroup.zpowers i, l * x * l⁻¹ ∈ Subgroup.zpowers i := by
      have hl_comm_i : Subgroup.zpowers i ≤ Subgroup.centralizer ({l} : Set (MulAut W)) := by
        rw [Subgroup.zpowers_le]
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact (hiL l hl).symm
      intro x hx
      have hx' : l * x = x * l := by
        have := hl_comm_i hx
        rw [Subgroup.mem_centralizer_iff] at this
        exact this l (Set.mem_singleton l)
      have : l * x * l⁻¹ = x := by rw [hx']; group
      rw [this]
      exact hx
    have hlU : ∀ u ∈ U, l u ∈ U := by
      intro u hu
      exact commSub_top_stable151b (X := L) (g := l)
        (by intro x hx; exact L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)) u hu
    induction hy using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨x, hx, w, hw, rfl⟩ := hc
      have : l (x w * w⁻¹) = (l * x * l⁻¹) (l w) * (l w)⁻¹ := by
        rw [map_mul, map_inv]
        simp [MulAut.mul_apply]
      rw [this]
      exact Subgroup.subset_closure ⟨l * x * l⁻¹, hl_norm_i x hx, l w, hlU w hw, rfl⟩
    | one => simp
    | mul a b _ _ iha ihb =>
      rw [map_mul]
      exact mul_mem iha ihb
    | inv a _ iha =>
      rw [map_inv]
      exact inv_mem iha
  have hY₂_inv : ∀ l ∈ L₂, ∀ y ∈ Y₂, l y ∈ Y₂ := by
    intro l hl y hy
    have hl_norm_i : ∀ x ∈ Subgroup.zpowers i, l * x * l⁻¹ ∈ Subgroup.zpowers i := by
      have hl_comm_i : Subgroup.zpowers i ≤ Subgroup.centralizer ({l} : Set (MulAut W)) := by
        rw [Subgroup.zpowers_le]
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact (hiL₂ l hl).symm
      intro x hx
      have hx' : l * x = x * l := by
        have := hl_comm_i hx
        rw [Subgroup.mem_centralizer_iff] at this
        exact this l (Set.mem_singleton l)
      have : l * x * l⁻¹ = x := by rw [hx']; group
      rw [this]
      exact hx
    have hlU₂ : ∀ u ∈ U₂, l u ∈ U₂ := by
      intro u hu
      exact commSub_top_stable151b (X := L₂) (g := l)
        (by intro x hx; exact L₂.mul_mem (L₂.mul_mem hl hx) (L₂.inv_mem hl)) u hu
    induction hy using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨x, hx, w, hw, rfl⟩ := hc
      have : l (x w * w⁻¹) = (l * x * l⁻¹) (l w) * (l w)⁻¹ := by
        rw [map_mul, map_inv]
        simp [MulAut.mul_apply]
      rw [this]
      exact Subgroup.subset_closure ⟨l * x * l⁻¹, hl_norm_i x hx, l w, hlU₂ w hw, rfl⟩
    | one => simp
    | mul a b _ _ iha ihb =>
      rw [map_mul]
      exact mul_mem iha ihb
    | inv a _ iha =>
      rw [map_inv]
      exact inv_mem iha
  have hY_fix : Y ⊓ fixV L = ⊥ := by
    have : Y ⊓ fixV L ≤ U ⊓ fixV L := inf_le_inf hY_le_U le_rfl
    rw [hfix] at this
    exact le_bot_iff.mp this
  have hY_even : Even (rk ↥Y) :=
    s16h_even_rk_of_fpf_three hW hL hY_inv hY_fix
  have hL₂ : Nat.card ↥L₂ = 3 := by rw [hB.card_eq, hL]
  have hfix₂ : commSub (⊤ : Subgroup W) L₂ ⊓ fixV L₂ = ⊥ := hB.fix_iff.mpr hfix
  have hY₂_fix : Y₂ ⊓ fixV L₂ = ⊥ := by
    have : Y₂ ⊓ fixV L₂ ≤ U₂ ⊓ fixV L₂ := inf_le_inf hY₂_le_U₂ le_rfl
    rw [hfix₂] at this
    exact le_bot_iff.mp this
  have hY₂_even : Even (rk ↥Y₂) :=
    s16h_even_rk_of_fpf_three hW hL₂ hY₂_inv hY₂_fix
  have h_inf_Y : Y ⊓ Y₂ = ⊥ := by
    have : Y ⊓ Y₂ ≤ U ⊓ U₂ := inf_le_inf hY_le_U hY₂_le_U₂
    rw [hB.inf] at this
    exact le_bot_iff.mp this
  have h_le_Y : Y ⊔ Y₂ ≤ commSub (⊤ : Subgroup W) (Subgroup.zpowers i) :=
    sup_le (commSub_mono le_top le_rfl) (commSub_mono le_top le_rfl)
  have h_sum : rk ↥Y + rk ↥Y₂ ≤ 2 := by
    have hs := rk_sup_add_rk_inf Y Y₂
    rw [h_inf_Y, rk_bot, add_zero] at hs
    rw [← hs]
    exact le_trans (rk_mono h_le_Y) hri
  obtain ⟨a, ha⟩ := hY_even
  obtain ⟨b, hb⟩ := hY₂_even
  have h_zero : rk ↥Y = 0 ∨ rk ↥Y₂ = 0 := by omega
  rcases h_zero with hY_zero | hY₂_zero
  · left
    rw [mem_centSub]
    intro u hu
    have hY_bot : Y = ⊥ := (rk_eq_zero_iff hW).mp hY_zero
    have : u ∈ fixV (Subgroup.zpowers i) := (commSub_eq_bot_iff.mp hY_bot) hu
    exact mem_fixV_zpowers_iff_apply.mp this
  · right
    rw [mem_centSub]
    intro u hu
    have hY₂_bot : Y₂ = ⊥ := (rk_eq_zero_iff hW).mp hY₂_zero
    have : u ∈ fixV (Subgroup.zpowers i) := (commSub_eq_bot_iff.mp hY₂_bot) hu
    exact mem_fixV_zpowers_iff_apply.mp this

theorem s16h_z3_conj_inv {W : Type} [CommGroup W] {A L L₂ : Subgroup (MulAut W)} {x : MulAut W}
    (hB : s16h_Z3Blocks A L L₂ x) {i : MulAut W}
    (hiU : i ∈ centSub (commSub (⊤ : Subgroup W) L)) (hiL₂ : ∀ l ∈ L₂, i * l = l * i) :
    x * i * x⁻¹ ∈ centSub (commSub (⊤ : Subgroup W) L₂) ∧
      ∀ l ∈ L, (x * i * x⁻¹) * l = l * (x * i * x⁻¹) := by
  let U := commSub (⊤ : Subgroup W) L
  let U₂ := commSub (⊤ : Subgroup W) L₂
  have hj_centU₂ : x * i * x⁻¹ ∈ centSub U₂ := by
    rw [mem_centSub]
    intro u₂ hu₂
    have hxinv : x⁻¹ u₂ ∈ U := (hB.swap (x⁻¹ u₂)).mpr (by simpa using hu₂)
    have hi : i (x⁻¹ u₂) = x⁻¹ u₂ := (mem_centSub.mp hiU) (x⁻¹ u₂) hxinv
    simp only [MulAut.mul_apply]
    rw [hi]
    exact MulAut.apply_inv_self W x u₂
  have hj_commL : ∀ l ∈ L, (x * i * x⁻¹) * l = l * (x * i * x⁻¹) := by
    have hL₂map : L₂.map (MulAut.conj x).toMonoidHom = L := by
      rcases hB.perm x hB.mem with h | h
      · exfalso
        exact hB.ne (hB.eq.trans h.1)
      · exact h.2
    intro l hl
    have hl' : l ∈ L₂.map (MulAut.conj x).toMonoidHom := by rw [hL₂map]; exact hl
    obtain ⟨l₂, hl₂, hl₂x⟩ := Subgroup.mem_map.mp hl'
    rw [← hl₂x]
    have hcomm : i * l₂ = l₂ * i := hiL₂ l₂ hl₂
    calc (x * i * x⁻¹) * (x * l₂ * x⁻¹)
      = x * (i * l₂) * x⁻¹ := by group
    _ = x * (l₂ * i) * x⁻¹ := by rw [hcomm]
    _ = (x * l₂ * x⁻¹) * (x * i * x⁻¹) := by group
  exact ⟨hj_centU₂, hj_commL⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
