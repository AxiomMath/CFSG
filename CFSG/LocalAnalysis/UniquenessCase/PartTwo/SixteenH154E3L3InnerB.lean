module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3InnerA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Lat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_e3_l3_split_isPSL {L : Subgroup (MulAut W)} {k : ℕ}
    (S : S16hL3Split L k) (hk : 1 ≤ k) : IsPSL 3 2 1 ↥L :=
  s16h_e3_l3_isPSL_of_coord (BinaryNaturalSL.toL3Coord (S.I_nat ⟨0, hk⟩))

private theorem s16h_e3_l3_commSub_top_inv (L : Subgroup (MulAut W)) :
    ∀ l ∈ L, ∀ u ∈ commSub (⊤ : Subgroup W) L, l u ∈ commSub (⊤ : Subgroup W) L := by
  intro l hl u hu
  induction hu using Subgroup.closure_induction with
  | mem c hc =>
      obtain ⟨x, hx, w, -, rfl⟩ := hc
      refine Subgroup.subset_closure ⟨l * x * l⁻¹, L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl),
        l w, Subgroup.mem_top _, ?_⟩
      simp [MulAut.mul_apply]
  | one => simpa using (commSub (⊤ : Subgroup W) L).one_mem
  | mul a b ha hb iha ihb => simpa [map_mul] using (commSub (⊤ : Subgroup W) L).mul_mem iha ihb
  | inv a ha ih => simpa [map_inv] using (commSub (⊤ : Subgroup W) L).inv_mem ih

private theorem s16h_e3_l3_commSub_top_self {L : Subgroup (MulAut W)} {k : ℕ}
    (S : S16hL3Split L k) : commSub (commSub ⊤ L) L = commSub ⊤ L := by
  refine le_antisymm (commSub_le_of_invariant (s16h_e3_l3_commSub_top_inv L)) ?_
  calc commSub (⊤ : Subgroup W) L = ⨆ i, S.J i := S.J_iSup.symm
    _ ≤ commSub (commSub ⊤ L) L := by
        refine iSup_le fun i => ?_
        rw [← S.J_comm i]
        exact commSub_mono ((le_iSup (fun i => S.J i) i).trans (le_of_eq S.J_iSup)) le_rfl

private theorem s16h_e3_l3_maps_commSub_top {L : Subgroup (MulAut W)} {c : MulAut W}
    (hcL : ∀ l ∈ L, c * l = l * c) :
    ∀ u ∈ commSub (⊤ : Subgroup W) L, c u ∈ commSub (⊤ : Subgroup W) L := by
  have hmem : ∀ y ∈ ({y : W | ∃ x ∈ L, ∃ w ∈ (⊤ : Subgroup W), x w * w⁻¹ = y}),
      c y ∈ commSub (⊤ : Subgroup W) L := by
    rintro y ⟨l, hl, w, -, rfl⟩
    refine Subgroup.subset_closure ⟨l, hl, c w, Subgroup.mem_top _, ?_⟩
    rw [map_mul, map_inv]
    congr 1
    calc l (c w) = (l * c) w := rfl
      _ = (c * l) w := by rw [(hcL l hl).symm]
      _ = c (l w) := rfl
  intro u hu
  have hsub : commSub (⊤ : Subgroup W) L ≤
      Subgroup.comap c.toMonoidHom (commSub (⊤ : Subgroup W) L) := by
    rw [commSub, Subgroup.closure_le]
    exact hmem
  exact hsub hu

private theorem s16h_e3_l3_commSub_zpowers_le_self {U : Subgroup W} {g : MulAut W}
    (hgU : ∀ u ∈ U, g u ∈ U) : commSub U (Subgroup.zpowers g) ≤ U := by
  have hpow : ∀ n : ℕ, ∀ w ∈ U, (g ^ n) w ∈ U := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
        intro w hw
        rw [pow_succ, MulAut.mul_apply]
        exact ih (g w) (hgU w hw)
  have hstab : ∀ x ∈ Subgroup.zpowers g, ∀ w ∈ U, x w ∈ U := by
    intro x hx w hw
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, g ^ n = x :=
      (Submonoid.mem_powers_iff x g).mp ((mem_powers_iff_mem_zpowers (x := g) (y := x)).mpr hx)
    exact hpow n w hw
  rw [commSub_zpowers_eq_map hstab]
  rintro x ⟨u, hu, rfl⟩
  rw [commHom_apply]
  exact U.mul_mem (hgU u hu) (U.inv_mem hu)

omit [Finite W] in
private theorem s16h_e3_l3_pow_eq_of_eq {X : Subgroup W} {g₁ g₂ : MulAut W}
    (hXinv : ∀ x ∈ X, g₁ x ∈ X) (h : ∀ x ∈ X, g₁ x = g₂ x) :
    ∀ n : ℕ, ∀ x ∈ X, (g₁ ^ n) x = (g₂ ^ n) x := by
  intro n
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
      intro x hx
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply,
        ih (g₁ x) (hXinv x hx), h x hx]

private theorem s16h_e3_l3_commSub_zpowers_congr {X : Subgroup W} {g₁ g₂ : MulAut W}
    (hstab₁ : ∀ x ∈ Subgroup.zpowers g₁, ∀ w ∈ X, x w ∈ X)
    (hstab₂ : ∀ x ∈ Subgroup.zpowers g₂, ∀ w ∈ X, x w ∈ X)
    (h : ∀ w ∈ X, g₁ w = g₂ w) :
    commSub X (Subgroup.zpowers g₁) = commSub X (Subgroup.zpowers g₂) := by
  rw [commSub_zpowers_eq_map hstab₁, commSub_zpowers_eq_map hstab₂]
  refine le_antisymm ?_ ?_
  · rintro x ⟨w, hw, rfl⟩
    exact ⟨w, hw, by rw [commHom_apply, commHom_apply, h w hw]⟩
  · rintro x ⟨w, hw, rfl⟩
    exact ⟨w, hw, by rw [commHom_apply, commHom_apply, h w hw]⟩

theorem s16h_e3_l3_rank_inner_of_invol (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {k : ℕ} (S : S16hL3Split L k) (hk : 2 ≤ k) {γ : MulAut W} (hγL : γ ∈ L) (hγ2 : γ ^ 2 = 1)
    (hγ1 : γ ≠ 1) :
    4 ≤ rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers γ)) := by
  have hL := s16h_e3_l3_split_isPSL S (by omega)
  let i₀ : Fin k := ⟨0, by omega⟩
  let i₁ : Fin k := ⟨1, by omega⟩
  have hbound : ∀ i : Fin k, 2 ≤ rk ↥(commSub (S.J i) (Subgroup.zpowers γ)) := by
    intro i
    have h := s16h_e3_l3_rk_le_three_mul_commSub_of_eq hL (S.J_inv i) (S.J_comm i) hγL hγ2 hγ1
    have h4 := S.J_rk i
    omega
  have hi10 : i₁ ≠ i₀ := by
    intro h
    have hval : (i₁ : ℕ) = (i₀ : ℕ) := by rw [h]
    simp [i₀, i₁] at hval
  have hJ1le : S.J i₁ ≤ ⨆ (j : Fin k) (_ : j ≠ i₀), S.J j :=
    le_iSup₂ (f := fun j (_ : j ≠ i₀) => S.J j) i₁ hi10
  have hJ01 : S.J i₀ ⊓ S.J i₁ = ⊥ := by
    refine le_antisymm ?_ bot_le
    calc S.J i₀ ⊓ S.J i₁ ≤ S.J i₀ ⊓ ⨆ (j : Fin k) (_ : j ≠ i₀), S.J j :=
          le_inf inf_le_left (inf_le_right.trans hJ1le)
      _ = ⊥ := S.J_ind i₀
  have hJ0U : S.J i₀ ≤ commSub ⊤ L := (le_iSup (fun i => S.J i) i₀).trans (le_of_eq S.J_iSup)
  have hJ1U : S.J i₁ ≤ commSub ⊤ L := (le_iSup (fun i => S.J i) i₁).trans (le_of_eq S.J_iSup)
  have h0 : commSub (S.J i₀) (Subgroup.zpowers γ) ≤ S.J i₀ :=
    commSub_le_of_invariant
      (fun x hx w hw => S.J_inv i₀ x (Subgroup.zpowers_le.mpr hγL hx) w hw)
  have h1 : commSub (S.J i₁) (Subgroup.zpowers γ) ≤ S.J i₁ :=
    commSub_le_of_invariant
      (fun x hx w hw => S.J_inv i₁ x (Subgroup.zpowers_le.mpr hγL hx) w hw)
  have hinf : commSub (S.J i₀) (Subgroup.zpowers γ) ⊓
      commSub (S.J i₁) (Subgroup.zpowers γ) = ⊥ := by
    refine le_antisymm ?_ bot_le
    calc _ ≤ S.J i₀ ⊓ S.J i₁ := le_inf (inf_le_left.trans h0) (inf_le_right.trans h1)
      _ = ⊥ := hJ01
  have hsup_le : commSub (S.J i₀) (Subgroup.zpowers γ) ⊔
      commSub (S.J i₁) (Subgroup.zpowers γ) ≤
      commSub (commSub ⊤ L) (Subgroup.zpowers γ) :=
    sup_le (commSub_mono hJ0U le_rfl) (commSub_mono hJ1U le_rfl)
  have hrank := rk_sup_add_rk_inf (commSub (S.J i₀) (Subgroup.zpowers γ))
    (commSub (S.J i₁) (Subgroup.zpowers γ))
  rw [hinf, rk_bot, add_zero] at hrank
  have hle := rk_mono hsup_le
  have h20 := hbound i₀
  have h21 := hbound i₁
  omega

theorem s16h_e3_l3_rank_cent (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {k : ℕ}
    (S : S16hL3Split L k) (hk : 1 ≤ k) {c : MulAut W} (hc2 : c ^ 2 = 1)
    (hcL : ∀ l ∈ L, c * l = l * c) (hcC : c ∉ centSub (commSub ⊤ L)) :
    4 ≤ rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers c)) := by
  have hL := s16h_e3_l3_split_isPSL S hk
  have hUinv := s16h_e3_l3_commSub_top_inv L
  have hUc := s16h_e3_l3_commSub_top_self S
  have hcU : ∀ u ∈ commSub ⊤ L, c u ∈ commSub ⊤ L := s16h_e3_l3_maps_commSub_top hcL
  have hcC' : ∃ u ∈ commSub ⊤ L, c u ≠ u := by
    by_contra h
    apply hcC
    rw [mem_centSub]
    intro u hu
    by_contra hcu
    exact h ⟨u, hu, hcu⟩
  set M : Subgroup W := commSub (commSub ⊤ L) (Subgroup.zpowers c) with hMdef
  obtain ⟨hMinv, hMcomm, hMfix, -⟩ := s16h_e3_l3_commSub_cent hW hUinv hUc hc2 hcL hcU
  rw [← hMdef] at hMinv hMcomm hMfix
  have hMne : M ≠ ⊥ := by
    intro hbot
    obtain ⟨u, hu, hcu⟩ := hcC'
    have hfix : u ∈ fixV (Subgroup.zpowers c) := (commSub_eq_bot_iff.mp hbot) hu
    exact hcu (mem_fixV_zpowers_iff.mp hfix)
  have hUniv : (⨆ j ∈ (Finset.univ : Finset (Fin k)), S.J j) = commSub ⊤ L := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun j => iSup_le fun _ => ?_
      exact (le_iSup (fun j => S.J j) j).trans (le_of_eq S.J_iSup)
    · rw [← S.J_iSup]
      exact iSup_le fun j =>
        le_iSup₂ (f := fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => S.J j) j
          (Finset.mem_univ j)
  have hXT : M ≤ ⨆ j ∈ (Finset.univ : Finset (Fin k)), S.J j := by
    rw [hUniv]
    exact s16h_e3_l3_commSub_zpowers_le_self hcU
  have hinv_ne : M ⊓ fixV L ≠ ⊥ :=
    s16h_e3_l3_inf_fixV_ne_bot hW S Finset.univ hXT hMinv hMne
  have h1 : 1 ≤ rk ↥(M ⊓ fixV L) := by
    by_contra h
    have h0 : rk ↥(M ⊓ fixV L) = 0 := by omega
    exact hinv_ne ((rk_eq_zero_iff hW).mp h0)
  have hnt : ∃ l ∈ L, ∃ x ∈ M, l x * x⁻¹ ∉ M ⊓ fixV L := by
    obtain ⟨l, hl, m, hm, hlm⟩ :=
      s16h_e3_l3_commSub_cent_nontriv hW hUinv hUc hc2 hcL hcU hcC'
    exact ⟨l, hl, m, hm, fun hmem => hlm hmem.2⟩
  have hYinv : ∀ l ∈ L, ∀ y ∈ M ⊓ fixV L, l y ∈ M ⊓ fixV L := by
    intro l hl y hy
    refine ⟨hMinv l hl y hy.1, ?_⟩
    rw [(mem_fixV.mp hy.2) l hl]
    exact hy.2
  have h3 := s16h_e3_l3_rk_add_three_le hW hL hMinv hYinv inf_le_left hnt
  omega

theorem s16h_e3_l3_rank_mixed (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {k : ℕ}
    (S : S16hL3Split L k) (hk : 1 ≤ k) {γ c : MulAut W} (hγL : γ ∈ L) (hγ2 : γ ^ 2 = 1)
    (hγ1 : γ ≠ 1) (hc2 : c ^ 2 = 1) (hcL : ∀ l ∈ L, c * l = l * c)
    (hcC : c ∉ centSub (commSub ⊤ L)) :
    4 ≤ rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c))) := by
  have hL := s16h_e3_l3_split_isPSL S hk
  have hUinv := s16h_e3_l3_commSub_top_inv L
  have hUc := s16h_e3_l3_commSub_top_self S
  have hcU : ∀ u ∈ commSub ⊤ L, c u ∈ commSub ⊤ L := s16h_e3_l3_maps_commSub_top hcL
  set M : Subgroup W := commSub (commSub ⊤ L) (Subgroup.zpowers c) with hMdef
  obtain ⟨hMinv, hMcomm, hMfix, h2M⟩ :=
    s16h_e3_l3_commSub_cent hW hUinv hUc hc2 hcL hcU
  rw [← hMdef] at hMinv hMcomm hMfix h2M
  have hM4 : 4 ≤ rk ↥M := by
    have h := s16h_e3_l3_rank_cent hW S hk hc2 hcL hcC
    rwa [← hMdef] at h
  have hMU : M ≤ commSub ⊤ L := s16h_e3_l3_commSub_zpowers_le_self hcU
  have hcM : ∀ m ∈ M, c m = m := fun m hm => mem_fixV_zpowers_iff.mp (hMfix hm)
  have hγτ : ∀ m ∈ M, γ m = (γ * c) m := by
    intro m hm
    rw [MulAut.mul_apply, hcM m hm]
  have hτM : ∀ m ∈ M, (γ * c) m ∈ M := by
    intro m hm
    rw [← hγτ m hm]
    exact hMinv γ hγL m hm
  have hstabγM : ∀ x ∈ Subgroup.zpowers γ, ∀ w ∈ M, x w ∈ M :=
    fun x hx w hw => hMinv x (Subgroup.zpowers_le.mpr hγL hx) w hw
  have hstabτM : ∀ x ∈ Subgroup.zpowers (γ * c), ∀ w ∈ M, x w ∈ M := by
    intro x hx w hw
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, (γ * c) ^ n = x :=
      (Submonoid.mem_powers_iff x (γ * c)).mp
        ((mem_powers_iff_mem_zpowers (x := γ * c) (y := x)).mpr hx)
    rw [s16h_e3_l3_pow_eq_of_eq (X := M) hτM (fun x hx => (hγτ x hx).symm) n w hw]
    exact hMinv (γ ^ n) (Subgroup.pow_mem L hγL n) w hw
  have hMγ_le : commSub M (Subgroup.zpowers γ) ≤
      commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) := by
    calc commSub M (Subgroup.zpowers γ) = commSub M (Subgroup.zpowers (γ * c)) :=
          (s16h_e3_l3_commSub_zpowers_congr hstabτM hstabγM
            (fun w hw => (hγτ w hw).symm)).symm
      _ ≤ commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) := commSub_mono hMU le_rfl
  have hstabγU : ∀ x ∈ Subgroup.zpowers γ, ∀ w ∈ commSub ⊤ L, x w ∈ commSub ⊤ L :=
    fun x hx w hw => hUinv x (Subgroup.zpowers_le.mpr hγL hx) w hw
  have hUγ_le : commSub (commSub ⊤ L) (Subgroup.zpowers γ) ≤
      commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) ⊔ M := by
    rw [commSub_zpowers_eq_map hstabγU]
    rintro x ⟨u, hu, rfl⟩
    rw [commHom_apply]
    have h1 : (γ * c) u * u⁻¹ ∈ commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) :=
      Subgroup.subset_closure ⟨γ * c, Subgroup.mem_zpowers (γ * c), u, hu, rfl⟩
    have hmem : c u * u⁻¹ ∈ M := by
      show c u * u⁻¹ ∈ commSub (commSub ⊤ L) (Subgroup.zpowers c)
      exact Subgroup.subset_closure ⟨c, Subgroup.mem_zpowers c, u, hu, rfl⟩
    have h2 : (γ (c u * u⁻¹))⁻¹ ∈ M := Subgroup.inv_mem _ (hMinv γ hγL _ hmem)
    have heq : γ u * u⁻¹ = ((γ * c) u * u⁻¹) * (γ (c u * u⁻¹))⁻¹ := by
      rw [MulAut.mul_apply, map_mul, map_inv, mul_inv_rev, inv_inv]
      calc γ u * u⁻¹ = (γ u * u⁻¹) * (γ (c u) * (γ (c u))⁻¹) := by
            rw [mul_inv_cancel, mul_one]
        _ = (γ (c u) * u⁻¹) * (γ u * (γ (c u))⁻¹) := by ac_rfl
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  have hMγ2 : 2 ≤ rk ↥(commSub M (Subgroup.zpowers γ)) := by
    have h := s16h_e3_l3_rk_le_three_mul_commSub_of_eq hL hMinv hMcomm hγL hγ2 hγ1
    set y : ℕ := rk ↥(commSub M (Subgroup.zpowers γ))
    set x : ℕ := rk ↥M
    omega
  have hXgen : commSub (commSub ⊤ L) L ⊔ M = commSub ⊤ L := by
    rw [hUc]
    exact sup_eq_left.mpr hMU
  have hUX : rk ↥(commSub ⊤ L) + 2 * rk ↥M ≤
      3 * rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers γ) ⊔ M) :=
    s16h_e3_l3_rk_le_three_mul_commSub hL hUinv hMinv hXgen hγL hγ2 hγ1
  have hle1 : commSub M (Subgroup.zpowers γ) ≤
      commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) ⊓ M :=
    le_inf hMγ_le (commSub_le_of_invariant hstabγM)
  have hle2 : commSub (commSub ⊤ L) (Subgroup.zpowers γ) ⊔ M ≤
      commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) ⊔ M :=
    sup_le hUγ_le le_sup_right
  have hY_lb : rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) ⊓ M) ≥
      rk ↥(commSub M (Subgroup.zpowers γ)) := rk_mono hle1
  have hX_lb : rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) ⊔ M) ≥
      rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers γ) ⊔ M) := rk_mono hle2
  have hx_lb : rk ↥M + 2 ≤
      rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers γ) ⊔ M) := by
    set x : ℕ := rk ↥M
    set u : ℕ := rk ↥(commSub ⊤ L)
    set z : ℕ := rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers γ) ⊔ M)
    omega
  have ha : rk ↥M + 2 ≤
      rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) ⊔ M) := hx_lb.trans hX_lb
  have hb : 2 ≤ rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) ⊓ M) :=
    hMγ2.trans hY_lb
  have hsum :=
    rk_sup_add_rk_inf (commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c))) M
  have hlower : rk ↥M + 4 ≤
      rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) ⊔ M) +
        rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) ⊓ M) := by
    set x : ℕ := rk ↥M
    set a : ℕ := rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) ⊔ M)
    set b : ℕ := rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) ⊓ M)
    omega
  change 4 ≤ rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)))
  set x : ℕ := rk ↥M
  set y : ℕ := rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)))
  set a : ℕ := rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) ⊔ M)
  set b : ℕ := rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers (γ * c)) ⊓ M)
  omega

theorem s16h_e3_l3_rank_inner (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {k : ℕ}
    (S : S16hL3Split L k) (hk : 2 ≤ k) {τ : MulAut W} (hτ2 : τ ^ 2 = 1)
    (hτC : τ ∉ centSub (commSub ⊤ L)) {γ : MulAut W} (hγL : γ ∈ L)
    (hinn : ∀ l ∈ L, τ * l * τ⁻¹ = γ * l * γ⁻¹) :
    4 ≤ rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers τ)) := by
  have hL := s16h_e3_l3_split_isPSL S (by omega)
  obtain ⟨hγ2, hc2, hcL⟩ := s16h_e3_l3_inner_decomp hL hτ2 hγL hinn
  by_cases hγ1 : γ = 1
  · have hc_eq : γ⁻¹ * τ = τ := by rw [hγ1, inv_one, one_mul]
    have hcC : γ⁻¹ * τ ∉ centSub (commSub ⊤ L) := by rwa [hc_eq]
    have h := s16h_e3_l3_rank_cent hW S (by omega) hc2 hcL hcC
    rwa [hc_eq] at h
  · by_cases hcU : γ⁻¹ * τ ∈ centSub (commSub ⊤ L)
    · have hcfix : ∀ u ∈ commSub ⊤ L, (γ⁻¹ * τ) u = u :=
        fun u hu => (mem_centSub.mp hcU) u hu
      have hγτ : ∀ u ∈ commSub ⊤ L, τ u = γ u := by
        intro u hu
        have h1 : γ * (γ⁻¹ * τ) = τ := by group
        calc τ u = (γ * (γ⁻¹ * τ)) u := by rw [h1]
          _ = γ ((γ⁻¹ * τ) u) := rfl
          _ = γ u := by rw [hcfix u hu]
      have hstabγ : ∀ x ∈ Subgroup.zpowers γ, ∀ w ∈ commSub ⊤ L, x w ∈ commSub ⊤ L :=
        fun x hx w hw => s16h_e3_l3_commSub_top_inv L x
          (Subgroup.zpowers_le.mpr hγL hx) w hw
      have hτU : ∀ u ∈ commSub ⊤ L, τ u ∈ commSub ⊤ L := by
        intro u hu
        rw [hγτ u hu]
        exact s16h_e3_l3_commSub_top_inv L γ hγL u hu
      have hstabτ : ∀ x ∈ Subgroup.zpowers τ, ∀ w ∈ commSub ⊤ L, x w ∈ commSub ⊤ L := by
        intro x hx w hw
        obtain ⟨n, rfl⟩ : ∃ n : ℕ, τ ^ n = x :=
          (Submonoid.mem_powers_iff x τ).mp
            ((mem_powers_iff_mem_zpowers (x := τ) (y := x)).mpr hx)
        rw [s16h_e3_l3_pow_eq_of_eq (X := commSub ⊤ L) hτU hγτ n w hw]
        exact s16h_e3_l3_commSub_top_inv L (γ ^ n) (Subgroup.pow_mem L hγL n) w hw
      have hcomm_eq := s16h_e3_l3_commSub_zpowers_congr (X := commSub ⊤ L)
        (g₁ := τ) (g₂ := γ) hstabτ hstabγ hγτ
      rw [hcomm_eq]
      exact s16h_e3_l3_rank_inner_of_invol hW S hk hγL hγ2 hγ1
    · have hmixed := s16h_e3_l3_rank_mixed hW S (by omega) hγL hγ2 hγ1 hc2 hcL hcU
      have h1 : γ * (γ⁻¹ * τ) = τ := by group
      rwa [h1] at hmixed

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
