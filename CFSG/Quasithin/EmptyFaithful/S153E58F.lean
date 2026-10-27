module

public import CFSG.Quasithin.EmptyFaithful.T1531Geom
public import CFSG.Quasithin.EmptyFaithful.S153E52C
public import CFSG.Quasithin.EmptyFaithful.S153E57G
public import CFSG.Quasithin.EmptyFaithful.S153E58B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E58

open S153E57

section VStar

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem exists_a {cx : Ctx15350 T Mc M V₁ V₂ t} (c : Chain15356 cx N₁ N₂ g s y t₁) :
    ∃ a : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)),
      a ∈ XStar153 T M V₁ Mc (VZ T M) ∧ a ≠ 1 ∧ a ^ 2 = 1 ∧
        XStar153 T M V₁ Mc (VZ T M) = Subgroup.zpowers a := by
  obtain ⟨v, hv, hv1, huniq⟩ := exists_v c
  have hv2 : v ^ 2 = 1 := by
    have hmem : v ^ 2 ∈ XStar153 T M V₁ Mc (VZ T M) := (XStar153 T M V₁ Mc (VZ T M)).pow_mem hv 2
    rcases huniq _ hmem with h | h
    · exact h
    · exfalso
      apply hv1
      have : v * v = v := by rw [← pow_two]; exact h
      exact mul_eq_right.1 this
  refine ⟨v, hv, hv1, hv2, le_antisymm (fun w hw => ?_) (Subgroup.zpowers_le.2 hv)⟩
  rcases huniq w hw with rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers _

theorem a_mem_HStar (cx : Ctx15350 T Mc M V₁ V₂ t)
    {a : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))}
    (ha : a ∈ XStar153 T M V₁ Mc (VZ T M)) : a ∈ HStar153 T M V₁ Mc :=
  XStar_le_HStar cx cx.hF.V_le_H ha

theorem a_mem_T (cx : Ctx15350 T Mc M V₁ V₂ t)
    {a : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))}
    (ha : a ∈ XStar153 T M V₁ Mc (VZ T M)) :
    a ∈ autOn (tildeOf (quasithinOmegaOneCenter T) T)
      (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
  A4.autOn_mono (secImg_mono cx.hF.V_le_T) ha

theorem a_central (cx : Ctx15350 T Mc M V₁ V₂ t)
    {a : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))}
    (ha1 : a ≠ 1) (hV : XStar153 T M V₁ Mc (VZ T M) = Subgroup.zpowers a)
    (hV2 : ∀ w ∈ XStar153 T M V₁ Mc (VZ T M), w = 1 ∨ w = a)
    (x : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))
    (hx : x ∈ autOn (tildeOf (quasithinOmegaOneCenter T) T)
      (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) : x * a = a * x := by
  have hn : autOn (tildeOf (quasithinOmegaOneCenter T) T)
        (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) ≤
      Subgroup.normalizer (autOn (tildeOf (quasithinOmegaOneCenter T) (VZ T M))
        (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) : Set _) :=
    autOn_le_normalizer_autOn (HypF91.tilde_le_normalizer (hBH := cx.hF.T_le_H))
      (HypF91.tilde_le_normalizer (hBH := cx.hF.V_le_H)) (S153E.tildeT_le_normalizer_tildeV cx)
  have ha : a ∈ XStar153 T M V₁ Mc (VZ T M) := hV ▸ Subgroup.mem_zpowers a
  have hxa : x * a * x⁻¹ ∈ XStar153 T M V₁ Mc (VZ T M) :=
    (Subgroup.mem_normalizer_iff.1 (hn hx) a).1 ha
  rcases hV2 _ hxa with h | h
  · exfalso
    apply ha1
    have : x * a = x := by
      calc x * a = (x * a * x⁻¹) * x := by group
        _ = x := by rw [h, one_mul]
    exact mul_eq_left.1 this
  · calc x * a = (x * a * x⁻¹) * x := by group
      _ = a * x := by rw [h]

end VStar

section Perp

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

noncomputable abbrev Pt (T M V₁ Mc : Subgroup G) :
    Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
  (tildeOf (quasithinOmegaOneCenter T) (VZ T M ⊓ UH153 T M V₁ Mc)).subgroupOf
    (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))

theorem Z_le_P (cx : Ctx15350 T Mc M V₁ V₂ t) :
    quasithinOmegaOneCenter T ≤ VZ T M ⊓ UH153 T M V₁ Mc :=
  le_inf cx.c.hyp.Z_le_VZ ((S153E.Z_le_ZS cx).trans (S153E.ZS_le_U cx))

theorem mem_Pt_iff (cx : Ctx15350 T Mc M V₁ V₂ t) (u : ↥(UH153 T M V₁ Mc)) :
    piU cx u ∈ Pt T M V₁ Mc ↔ (u : G) ∈ VZ T M ⊓ UH153 T M V₁ Mc := by
  rw [Subgroup.mem_subgroupOf]
  show ((piU cx u : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    SecQuot (NZ T) (quasithinOmegaOneCenter T)) ∈ tildeOf (quasithinOmegaOneCenter T) _ ↔ _
  rw [piU_coe]
  exact secMk_mem_secImg_iff (A := NZ T) (B := quasithinOmegaOneCenter T) (Z_le_P cx)

theorem rho_mul_inv_piU (cx : Ctx15350 T Mc M V₁ V₂ t) (n : NZ T) (hn : (n : G) ∈ Mc)
    (u : ↥(UH153 T M V₁ Mc)) :
    rho cx n (piU cx u) * (piU cx u)⁻¹ =
      piU cx ⟨(n : G) * u * (n : G)⁻¹ * (u : G)⁻¹,
        Subgroup.mul_mem _ (S153E.U_conj_mem hn u.2) (Subgroup.inv_mem _ u.2)⟩ := by
  have h := piU_conj cx n hn u
  have e : (⟨(n : G) * u * (n : G)⁻¹ * (u : G)⁻¹,
      Subgroup.mul_mem _ (S153E.U_conj_mem hn u.2) (Subgroup.inv_mem _ u.2)⟩ : ↥(UH153 T M V₁ Mc)) =
      ⟨(n : G) * u * (n : G)⁻¹, S153E.U_conj_mem hn u.2⟩ * u⁻¹ := rfl
  rw [e, map_mul, map_inv, h]

theorem commIn153_eq_Pt (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁) :
    commIn153 (XStar153 T M V₁ Mc (VZ T M))
      (⊤ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) = Pt T M V₁ Mc := by
  obtain ⟨P, -, hVQ, hVU, hUV⟩ := c.h53two.perp
  have hPeq : P = VZ T M ⊓ UH153 T M V₁ Mc := hVU.symm
  have hMc : ∀ n : NZ T, (n : G) ∈ Mc := fun n => NZ_le_Mc cx n.2
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨a', ha', w, -, rfl⟩
    obtain ⟨n, hnV, rfl⟩ := (mem_XStar_iff cx _ _).1 ha'
    obtain ⟨u, rfl⟩ := piU_surjective cx w
    show rho cx n (piU cx u) * (piU cx u)⁻¹ ∈ Pt T M V₁ Mc
    rw [rho_mul_inv_piU cx n (hMc n) u, mem_Pt_iff]
    refine ⟨?_, Subgroup.mul_mem _ (S153E.U_conj_mem (hMc n) u.2) (Subgroup.inv_mem _ u.2)⟩
    have h1 : ⁅(n : G), (u : G)⁆ ∈ ⁅VZ T M, UH153 T M V₁ Mc⁆ :=
      Subgroup.commutator_mem_commutator hnV u.2
    rw [Subgroup.commutator_comm, hUV, hPeq] at h1
    exact h1.1
  · intro w hw
    obtain ⟨u, rfl⟩ := piU_surjective cx w
    have hu : (u : G) ∈ ⁅UH153 T M V₁ Mc, VZ T M⁆ := by
      rw [hUV, hPeq]
      exact (mem_Pt_iff cx u).1 hw
    have key : ∀ x ∈ ⁅UH153 T M V₁ Mc, VZ T M⁆, ∃ hx : x ∈ UH153 T M V₁ Mc,
        piU cx ⟨x, hx⟩ ∈ commIn153 (XStar153 T M V₁ Mc (VZ T M))
          (⊤ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) := by
      intro x hx
      rw [Subgroup.commutator_def] at hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨u', hu', v, hv, rfl⟩ := hx
        have hvT : v ∈ T := cx.hF.V_le_T hv
        have hvMc : v ∈ Mc := S153E.T_le_Mc cx hvT
        have hvN : v ∈ NZ T := Mc_le_NZ cx hvMc
        let n : NZ T := ⟨v, hvN⟩
        let u1 : ↥(UH153 T M V₁ Mc) := ⟨u', hu'⟩
        have hcomm : v * u' * v⁻¹ * u'⁻¹ ∈ UH153 T M V₁ Mc :=
          Subgroup.mul_mem _ (S153E.U_conj_mem hvMc hu') (Subgroup.inv_mem _ hu')
        have e : ⁅u', v⁆ = (v * u' * v⁻¹ * u'⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
        have hUm : ⁅u', v⁆ ∈ UH153 T M V₁ Mc := by
          rw [e]
          exact Subgroup.inv_mem _ hcomm
        refine ⟨hUm, ?_⟩
        have hVn : rho cx n ∈ XStar153 T M V₁ Mc (VZ T M) := rho_mem_XStar cx n hv
        have h1 : rho cx n (piU cx u1) * (piU cx u1)⁻¹ ∈ commIn153 (XStar153 T M V₁ Mc (VZ T M))
            (⊤ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :=
          Subgroup.subset_closure ⟨_, hVn, piU cx u1, Subgroup.mem_top _, rfl⟩
        have h2 := Subgroup.inv_mem _ h1
        rw [rho_mul_inv_piU cx n hvMc u1] at h2
        have e2 : (⟨⁅u', v⁆, hUm⟩ : ↥(UH153 T M V₁ Mc)) =
            ⟨(n : G) * u1 * (n : G)⁻¹ * (u1 : G)⁻¹, Subgroup.mul_mem _ (S153E.U_conj_mem hvMc u1.2)
              (Subgroup.inv_mem _ u1.2)⟩⁻¹ := Subtype.ext e
        rw [e2, map_inv]
        exact h2
      | one =>
        refine ⟨Subgroup.one_mem _, ?_⟩
        have : (⟨1, Subgroup.one_mem _⟩ : ↥(UH153 T M V₁ Mc)) = 1 := rfl
        rw [this, map_one]
        exact Subgroup.one_mem _
      | mul x y _ _ ihx ihy =>
        obtain ⟨hx, hx'⟩ := ihx
        obtain ⟨hy, hy'⟩ := ihy
        refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
        have : (⟨x * y, Subgroup.mul_mem _ hx hy⟩ : ↥(UH153 T M V₁ Mc)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
        rw [this, map_mul]
        exact Subgroup.mul_mem _ hx' hy'
      | inv x _ ih =>
        obtain ⟨hx, hx'⟩ := ih
        refine ⟨Subgroup.inv_mem _ hx, ?_⟩
        have : (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : ↥(UH153 T M V₁ Mc)) = ⟨x, hx⟩⁻¹ := rfl
        rw [this, map_inv]
        exact Subgroup.inv_mem _ hx'
    obtain ⟨hx, hx'⟩ := key _ hu
    exact hx'

theorem card_P (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(VZ T M ⊓ UH153 T M V₁ Mc) = 8 := by
  obtain ⟨P, -, hVQ, hVU, -⟩ := c.h53two.perp
  have hV16 : Nat.card ↥(VZ T M) = 16 := cx.c.hyp.card_VZ
  have hPV : P ≤ VZ T M := hVQ ▸ inf_le_left
  have hrel : P.relIndex (VZ T M) = 2 := by
    rw [← hVQ]
    exact c.h53two.card_Vstar
  have e := Subgroup.relIndex_mul_card P (VZ T M)
  rw [inf_eq_left.2 hPV, hrel, hV16] at e
  rw [hVU]
  omega

theorem card_Pt (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(Pt T M V₁ Mc) = 4 := by
  obtain ⟨P, -, hVQ, hVU, hUV⟩ := c.h53two.perp
  have hV16 : Nat.card ↥(VZ T M) = 16 := cx.c.hyp.card_VZ
  have hPV : P ≤ VZ T M := hVQ ▸ inf_le_left
  have hPU : P ≤ UH153 T M V₁ Mc := hVU ▸ inf_le_right
  have hrel : P.relIndex (VZ T M) = 2 := by
    rw [← hVQ]
    exact c.h53two.card_Vstar
  have hP8 : Nat.card ↥P = 8 := by
    have e := Subgroup.relIndex_mul_card P (VZ T M)
    rw [inf_eq_left.2 hPV, hrel, hV16] at e
    omega
  have hPeq : P = VZ T M ⊓ UH153 T M V₁ Mc := hVU.symm
  have hZP : quasithinOmegaOneCenter T ≤ P := hPeq ▸ Z_le_P cx
  have hPN : P ≤ NZ T := hPV.trans (cx.hF.V_le_T.trans ((S153E.T_le_Mc cx).trans (Mc_le_NZ cx)))
  have h4 : Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) P) = 4 := by
    have h := relIndex_secImg (A := NZ T) (B := quasithinOmegaOneCenter T)
      (T := quasithinOmegaOneCenter T) (H := P) le_rfl hZP hPN
    have hbot : secImg (NZ T) (quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = ⊥ :=
      tildeOf_Z_eq_bot _
    rw [hbot, Subgroup.relIndex_bot_left] at h
    have e := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) P
    rw [inf_eq_left.2 hZP, Z_card cx, hP8] at e
    change Nat.card ↥(secImg (NZ T) (quasithinOmegaOneCenter T) P) = 4
    omega
  have hPle : tildeOf (quasithinOmegaOneCenter T) P ≤
      tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc) := secImg_mono hPU
  have hPt : Pt T M V₁ Mc =
      (tildeOf (quasithinOmegaOneCenter T) P).subgroupOf
        (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) := by
    rw [hPeq]
  rw [hPt]
  calc Nat.card ↥((tildeOf (quasithinOmegaOneCenter T) P).subgroupOf
          (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) =
        Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) P) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv
    _ = 4 := h4

theorem threePrime_N (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁) :
    ∀ h ∈ HStar153 T M V₁ Mc, orderOf h = 3 →
      ∃ r ∈ Pt T M V₁ Mc, h r ∉ Pt T M V₁ Mc := by
  intro h hh h3
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hnMc, rfl⟩ := (mem_XStar_iff cx Mc h).1 hh
  have hnP : ∀ x ∈ VZ T M ⊓ UH153 T M V₁ Mc,
      (n : G) * x * (n : G)⁻¹ ∈ VZ T M ⊓ UH153 T M V₁ Mc := by
    intro x hx
    have hxU : x ∈ UH153 T M V₁ Mc := hx.2
    have h1 : piU cx ⟨x, hxU⟩ ∈ Pt T M V₁ Mc := (mem_Pt_iff cx ⟨x, hxU⟩).2 hx
    have h2 := hcon _ h1
    rw [← piU_conj cx n hnMc ⟨x, hxU⟩] at h2
    exact (mem_Pt_iff cx _).1 h2
  have hnorm : (n : G) ∈ Subgroup.normalizer ((VZ T M ⊓ UH153 T M V₁ Mc : Subgroup G) : Set G) :=
    mem_normalizer_of_forall' hnP
  have hP8 := card_P cx c
  have hNM : Subgroup.normalizer ((VZ T M ⊓ UH153 T M V₁ Mc : Subgroup G) : Set G) ≤ M := by
    by_contra hnot
    have hbot : ⊥ < VZ T M ⊓ UH153 T M V₁ Mc := by
      refine bot_lt_iff_ne_bot.2 fun hb => ?_
      rw [hb, Subgroup.card_bot] at hP8
      omega
    have hlt : VZ T M ⊓ UH153 T M V₁ Mc < VZ T M := by
      refine lt_of_le_of_ne inf_le_left fun heq => ?_
      have := cx.c.hyp.card_VZ
      rw [← heq, hP8] at this
      omega
    have hts := cx.r46.totSingular_of_normalizer _ inf_le_left hbot hlt hnot
    exact not_isTotSingular153_of_card cx.c.hyp cx.c.decomp (by rw [hP8]) hts
  have hnM : (n : G) ∈ M := hNM hnorm
  have hthree : ¬ 3 ∣ Nat.card ↥(M ⊓ Mc) := cx.r49.threePrime_MH Mc (isHTM153_mc cx.c)
  have h1 : orderOf (n : G) ∣ Nat.card ↥(M ⊓ Mc) := by
    let x : ↥(M ⊓ Mc) := ⟨(n : G), hnM, hnMc⟩
    have h := orderOf_dvd_natCard x
    rw [← Subgroup.orderOf_coe x] at h
    exact h
  have h2 : orderOf (rho cx n) ∣ orderOf (n : G) := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_map_dvd (rho cx) n
  exact hthree ((h3 ▸ h2).trans h1)

theorem mem_tildeZS_iff (cx : Ctx15350 T Mc M V₁ V₂ t) (u : ↥(UH153 T M V₁ Mc)) :
    piU cx u ∈ S153E.tildeZS T M V₁ Mc ↔ (u : G) ∈ ZS153 T M V₁ := by
  rw [Subgroup.mem_subgroupOf]
  show ((piU cx u : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    SecQuot (NZ T) (quasithinOmegaOneCenter T)) ∈ tildeOf (quasithinOmegaOneCenter T) _ ↔ _
  rw [piU_coe]
  exact secMk_mem_secImg_iff (A := NZ T) (B := quasithinOmegaOneCenter T) (S153E.Z_le_ZS cx)

theorem threePrime_ZS (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ∀ h ∈ HStar153 T M V₁ Mc, orderOf h = 3 →
      ∃ z ∈ S153E.tildeZS T M V₁ Mc, h z ≠ z := by
  intro h hh h3
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hnMc, rfl⟩ := (mem_XStar_iff cx Mc h).1 hh
  have hnZ : ∀ z ∈ ZS153 T M V₁, (n : G) * z * (n : G)⁻¹ ∈ ZS153 T M V₁ := by
    intro z hz
    have hzU : z ∈ UH153 T M V₁ Mc := S153E.ZS_le_U cx hz
    have h1 : piU cx ⟨z, hzU⟩ ∈ S153E.tildeZS T M V₁ Mc := (mem_tildeZS_iff cx ⟨z, hzU⟩).2 hz
    have h2 := hcon _ h1
    rw [← piU_conj cx n hnMc ⟨z, hzU⟩] at h2
    have h3' : piU cx ⟨(n : G) * z * (n : G)⁻¹, S153E.U_conj_mem hnMc hzU⟩ ∈ S153E.tildeZS T M V₁ Mc := by
      rw [h2]
      exact h1
    exact (mem_tildeZS_iff cx _).1 h3'
  have hnorm : (n : G) ∈ Subgroup.normalizer (ZS153 T M V₁ : Set G) := mem_normalizer_of_forall' hnZ
  have hthree : ¬ 3 ∣ Nat.card ↥(Subgroup.normalizer (ZS153 T M V₁ : Set G)) := cx.r49.threePrime_N
  have h1 : orderOf (n : G) ∣ Nat.card ↥(Subgroup.normalizer (ZS153 T M V₁ : Set G)) := by
    let x : ↥(Subgroup.normalizer (ZS153 T M V₁ : Set G)) := ⟨(n : G), hnorm⟩
    have h := orderOf_dvd_natCard x
    rw [← Subgroup.orderOf_coe x] at h
    exact h
  have h2 : orderOf (rho cx n) ∣ orderOf (n : G) := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_map_dvd (rho cx) n
  exact hthree ((h3 ▸ h2).trans h1)

end Perp

end S153E58

end CFSG.Quasithin
