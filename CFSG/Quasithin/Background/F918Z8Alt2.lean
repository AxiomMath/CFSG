module

public import CFSG.Quasithin.Background.F918Z8h
public import CFSG.Quasithin.Background.F918Z8e
public import CFSG.Quasithin.Background.F918Z8d
public import CFSG.Quasithin.Background.F918Z8f

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Quot

variable {Y : Type} [CommGroup Y]

theorem d321q_orbSup_autQuot {Γ : Subgroup (MulAut Y)} {N V' : Subgroup Y} (hΓ : Γ ≤ stabSub N) :
    orbSup (autQuot Γ N) (V'.map (QuotientGroup.mk' N)) =
      (orbSup Γ V').map (QuotientGroup.mk' N) := by
  apply le_antisymm
  · refine orbSup_le fun φ hφ => ?_
    obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hφ
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨g.1 v, map_le_orbSup hg ⟨v, hv, rfl⟩, rfl⟩
  · rw [Subgroup.map_le_iff_le_comap]
    refine orbSup_le fun g hg => ?_
    rintro _ ⟨v, hv, rfl⟩
    exact map_le_orbSup (mem_autQuot.mpr ⟨⟨g, hΓ hg⟩, hg, rfl⟩)
      ⟨QuotientGroup.mk v, ⟨v, hv, rfl⟩, rfl⟩

theorem d321q_orbSup_mono {S T : Subgroup (MulAut Y)} {V : Subgroup Y} (h : S ≤ T) :
    orbSup S V ≤ orbSup T V :=
  orbSup_le fun _ hs => map_le_orbSup (h hs)

end Quot

section Tilde

variable {W : Type} [CommGroup W] {U Z A B : Subgroup W}

theorem d321q_tildeImg_mono (h : A ≤ B) : tildeImg U Z A ≤ tildeImg U Z B :=
  Subgroup.map_mono fun _ hx => h hx

theorem d321q_mem_sup {x : W} (hx : x ∈ U)
    (h : (QuotientGroup.mk ⟨x, hx⟩ : Sec U Z) ∈ tildeImg U Z B) : x ∈ B ⊔ Z := by
  obtain ⟨v, hv, hveq⟩ := h
  have h1 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hveq)
  have h2 := Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hv) h1
  rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at h2

theorem d321q_le_sup (hAU : A ≤ U) (h : tildeImg U Z A ≤ tildeImg U Z B) : A ≤ B ⊔ Z :=
  fun _ hx => d321q_mem_sup (hAU hx) (h ⟨⟨_, hAU hx⟩, hx, rfl⟩)

end Tilde

section Alt2

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d321q_norm (hL38 : D3L38) (hstd : D3Std M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) : D36Norm M Mp T L V t := by
  obtain ⟨-, hcomm, -, -⟩ := hL38 W M Mp T L V hstd t htT htL hMp
  have hnt := d321e_nontriv hstd hMp htriv (d321e_Lt_le_normalizer hcomm)
  exact ⟨hstd, d321e_lt htT htriv hnt, htT, htL, hMp, htriv⟩

theorem d321_comm_orbSup (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    commSub (orbSup T V) L = orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V :=
  d36_U_eq hL38 (d321q_norm hL38 hstd htT htL hMp htriv)

theorem d321_orbSup_alt (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    orbSup T V = orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V ⊔
      (orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V).map t.toMonoidHom := by
  have n := d321q_norm hL38 hstd htT htL hMp htriv
  refine le_antisymm (orbSup_le fun x hx => ?_)
    (sup_le (d321q_orbSup_mono inf_le_left) ?_)
  · rcases d36_split hL38 n x hx with h | h
    · have hxS : x ∈ T ⊓ Subgroup.normalizer (L : Set (MulAut W)) := ⟨hx, h⟩
      exact (map_le_orbSup (V := V) hxS).trans le_sup_left
    · have hs : t⁻¹ * x ∈ T ⊓ Subgroup.normalizer (L : Set (MulAut W)) :=
        ⟨T.mul_mem (T.inv_mem htT) hx, h⟩
      have h1 : V.map x.toMonoidHom ≤
          (orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V).map t.toMonoidHom := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨(t⁻¹ * x) v, map_le_orbSup hs ⟨v, hv, rfl⟩, ?_⟩
        simp [MulAut.mul_apply]
      exact h1.trans le_sup_right
  · rintro _ ⟨u, hu, rfl⟩
    exact mem_orbSup_of_mem_map htT (d321q_orbSup_mono inf_le_left hu)

theorem d321q_orbSup_le_commV (hL38 : D3L38)
    (hstd : D3Std M Mp T L V) (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V ≤ commV L := by
  rw [← d321_comm_orbSup hL38 hstd htT htL hMp htriv]
  exact (commSub_mono le_top le_rfl).trans (commV_eq_commSub L).ge

theorem d321q_L_stab_orbSup (hL38 : D3L38)
    (hstd : D3Std M Mp T L V) (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    ∀ x ∈ L, ∀ w ∈ orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V,
      x w ∈ orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V := by
  intro x hx w hw
  have hLMp : L ≤ Mp := by
    rw [hMp]
    exact le_sup_left
  have h := d321h_stab_commSub (d321e_Mp_le_stab_orbSup hstd (hLMp hx))
    (Subgroup.le_normalizer hx)
  rw [d321_comm_orbSup hL38 hstd htT htL hMp htriv] at h
  exact (mem_stabSub.mp h w).2 hw

theorem d321q_le_commSub (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V ≤
      commSub (orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V) L := by
  have h1 := d321_comm_orbSup hL38 hstd htT htL hMp htriv
  rw [d321_orbSup_alt hL38 hstd htT htL hMp htriv] at h1
  have hB : (orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V).map t.toMonoidHom ≤
      fixV L :=
    (Subgroup.map_mono (d321q_orbSup_le_commV hL38 hstd htT htL hMp htriv)).trans
      (d321h_map_le_fixV hL38 hstd htT htL hMp htriv)
  exact h1.symm.le.trans (d321h_commSub_sup_le hB)

omit [Finite W] in
theorem d321q_Z_le_fixV (hLMp : L ≤ Mp) : commV L ⊓ fixV Mp ≤ fixV L :=
  fun _ hz l hl => hz.2 l (hLMp hl)

omit [Finite W] in
theorem d321q_ML_stab_Z (hMpn : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))) :
    M ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub (commV L ⊓ fixV Mp) :=
  d321d_stabSub_inf (d321d_le_stabSub_commV inf_le_right)
    (d321d_le_stabSub_fixV (inf_le_left.trans hMpn))

omit [Finite W] in
theorem d321_tilde_hfix (hLMp : L ≤ Mp) :
    (commV L ⊓ fixV Mp).subgroupOf (commV L) ≤ fixV (autSub L (commV L)) := fun _ hz =>
  mem_fixV_autSub.mpr fun g hg _ => (Subgroup.mem_subgroupOf.mp hz).2 g (hLMp hg)

omit [Finite W] in
theorem d321_tilde_hZΓ (hMpn : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))) :
    autSub (M ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L) ≤
      stabSub ((commV L ⊓ fixV Mp).subgroupOf (commV L)) :=
  autSub_le_stabSub_subgroupOf (d321q_ML_stab_Z hMpn)

set_option linter.unusedVariables false in
theorem d321_tilde_orbSup (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    orbSup (autSec (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L) (commV L ⊓ fixV Mp))
        (tildeImg (commV L) (commV L ⊓ fixV Mp) V) =
      tildeImg (commV L) (commV L ⊓ fixV Mp)
        (orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V) := by
  have hVU : V ≤ commV L := d321h_le_commV hstd hMp htriv
  have hSML : T ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤
      M ⊓ Subgroup.normalizer (L : Set (MulAut W)) :=
    inf_le_inf_right _ hstd.hyp.sylow.1
  have hSU : T ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub (commV L) :=
    d321d_le_stabSub_commV inf_le_right
  have hSZ : T ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub (commV L ⊓ fixV Mp) :=
    hSML.trans (d321q_ML_stab_Z hstd.hyp.Mp_normal)
  have h1 := d321q_orbSup_autQuot (N := (commV L ⊓ fixV Mp).subgroupOf (commV L))
    (V' := V.subgroupOf (commV L)) (autSub_le_stabSub_subgroupOf hSZ)
  unfold autSec tildeImg
  rw [h1, d321e_orbSup_subgroupOf hVU hSU]

theorem d321_tilde_lt (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hstrict : V < orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V) :
    tildeImg (commV L) (commV L ⊓ fixV Mp) V <
      tildeImg (commV L) (commV L ⊓ fixV Mp)
        (orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V) := by
  have hLMp : L ≤ Mp := by
    rw [hMp]
    exact le_sup_left
  refine lt_of_le_of_ne (d321q_tildeImg_mono (le_orbSup _ V)) fun heq => ?_
  have hle : orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V ≤ V ⊔ (commV L ⊓ fixV Mp) :=
    d321q_le_sup (d321q_orbSup_le_commV hL38 hstd htT htL hMp htriv) heq.ge
  have hV : orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V ≤ V :=
    calc orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V
        ≤ commSub (orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V) L :=
          d321q_le_commSub hL38 hstd htT htL hMp htriv
      _ ≤ commSub (V ⊔ (commV L ⊓ fixV Mp)) L := commSub_mono hle le_rfl
      _ ≤ commSub V L := d321h_commSub_sup_le (d321q_Z_le_fixV hLMp)
      _ = V := d321_comm_eq hstd hMp htriv
  exact absurd hstrict (not_lt_of_ge hV)

theorem d321_tilde_top (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (h : tildeImg (commV L) (commV L ⊓ fixV Mp)
        (orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V) = ⊤) :
    orbSup T V = ⊤ := by
  have hLMp : L ≤ Mp := by
    rw [hMp]
    exact le_sup_left
  have hVSU := d321q_orbSup_le_commV hL38 hstd htT htL hMp htriv
  have hUle : commV L ≤
      orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V ⊔ (commV L ⊓ fixV Mp) := by
    intro u hu
    refine d321q_mem_sup hu ?_
    rw [h]
    trivial
  have htop := d321h_top_eq hL38 hstd htT htL hMp htriv
  have hUt := d321h_map_le_fixV hL38 hstd htT htL hMp htriv
  have hU1 : commV L ≤ commSub (commV L) L :=
    calc commV L = commSub ⊤ L := commV_eq_commSub L
      _ = commSub (commV L ⊔ (commV L).map t.toMonoidHom) L := by rw [htop]
      _ ≤ commSub (commV L) L := d321h_commSub_sup_le hUt
  have hUV : commV L ≤ orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V :=
    calc commV L ≤ commSub (commV L) L := hU1
      _ ≤ commSub (orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V ⊔
          (commV L ⊓ fixV Mp)) L := commSub_mono hUle le_rfl
      _ ≤ commSub (orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V) L :=
          d321h_commSub_sup_le (d321q_Z_le_fixV hLMp)
      _ ≤ orbSup (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) V :=
          commSub_le_of_invariant (d321q_L_stab_orbSup hL38 hstd htT htL hMp htriv)
  rw [d321_orbSup_alt hL38 hstd htT htL hMp htriv, le_antisymm hVSU hUV]
  exact htop

theorem d321_alt2_of_deep (hL38 : D3L38) (hDeep : D310Deep)
    (hstd : D3Std M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    {A : Subgroup (MulAut W)} (hA : QOff Mp T A (orbSup T V))
    (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hqS : qhatOf (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) ≤ ((2 : ℚ) : WithTop ℚ))
    (hstrict : V < commSub (orbSup T V) L) : orbSup T V = ⊤ := by
  have hLMp : L ≤ Mp := by
    rw [hMp]
    exact le_sup_left
  have hD1 := d3Std_restrict_U_gen hL38 hstd htT htL hMp htriv hqS
  have hfix := d321_tilde_hfix (Mp := Mp) hLMp
  have hZΓ := d321_tilde_hZΓ (L := L) hstd.hyp.Mp_normal
  have hD2 := d3Std_quot_gen hD1 hfix hZΓ
  have hq := d321_qhat_restrict hL38 hstd htT htL hMp hA htriv
  have hcomm := d321_comm_orbSup hL38 hstd htT htL hMp htriv
  rw [hcomm] at hstrict
  have hlt := d321_tilde_lt hL38 hstd htT htL hMp htriv hstrict
  rw [← d321_tilde_orbSup hL38 hstd htT htL hMp htriv] at hlt
  have htop := hDeep _ _ _ _ _ _ hD2 rfl hq hlt
  have htop' : orbSup (autSec (T ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L)
      (commV L ⊓ fixV Mp)) (tildeImg (commV L) (commV L ⊓ fixV Mp) V) = ⊤ := htop
  rw [d321_tilde_orbSup hL38 hstd htT htL hMp htriv] at htop'
  exact d321_tilde_top hL38 hstd htT htL hMp htriv htop'

end Alt2

end CFSG.Quasithin
