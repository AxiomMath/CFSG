module

public import CFSG.Quasithin.EmptyFaithful.S153E57F
public import CFSG.Quasithin.EmptyFaithful.S153E57C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E57

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem one_ne_of (cx : Ctx15350 T Mc M V₁ V₂ t) (h52 : Concl15352 cx) :
    quasithinOmegaOneCenter T < UH153 T M V₁ Mc := by
  refine lt_of_le_of_ne ((S153E.Z_le_ZS cx).trans (S153E.ZS_le_U cx)) fun h => ?_
  obtain ⟨a, ha, b, hb, hne⟩ := h52
  have hZe : IsElemAbelian 2 (quasithinOmegaOneCenter T) :=
    isElemAbelian_of_card_eq_two (Z_card cx)
  rw [← h] at ha hb
  exact hne (B2F.isElemAbelian_comm hZe ha hb)

theorem one_irr_of (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁)
    (W : Subgroup G) (hZW : quasithinOmegaOneCenter T ≤ W) (hWU : W ≤ UH153 T M V₁ Mc)
    (hMcW : Mc ≤ Subgroup.normalizer (W : Set G)) :
    W = quasithinOmegaOneCenter T ∨ W = UH153 T M V₁ Mc := by
  let B : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
    (W.subgroupOf (UH153 T M V₁ Mc)).map (piU cx)
  have hB : ∀ k ∈ HStar153 T M V₁ Mc, ∀ b ∈ B, k b ∈ B := by
    intro k hk b hb
    obtain ⟨n, hn, rfl⟩ := (mem_XStar_iff cx Mc k).1 hk
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hb
    have hwW : (w : G) ∈ W := Subgroup.mem_subgroupOf.1 hw
    rw [← piU_conj cx n hn w]
    refine Subgroup.mem_map.2 ⟨⟨(n : G) * w * (n : G)⁻¹, S153E.U_conj_mem hn w.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.1 (hMcW hn) w).1 hwW
  rcases (irr_H cx c).2.2 B le_top hB with h | h
  · left
    refine le_antisymm (fun w hw => ?_) hZW
    have hwU := hWU hw
    have hmem : piU cx ⟨w, hwU⟩ ∈ B :=
      Subgroup.mem_map.2 ⟨⟨w, hwU⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact (piU_eq_one_iff cx _).1 hmem
  · right
    refine le_antisymm hWU (fun u hu => ?_)
    have hmem : piU cx ⟨u, hu⟩ ∈ B := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hmem
    have hwW : (w : G) ∈ W := Subgroup.mem_subgroupOf.1 hw
    have hZ : ((w⁻¹ * ⟨u, hu⟩ : ↥(UH153 T M V₁ Mc)) : G) ∈ quasithinOmegaOneCenter T :=
      (piU_eq_one_iff cx _).1 (by rw [map_mul, map_inv, hwu]; exact inv_mul_cancel _)
    have e : u = (w : G) * ((w⁻¹ * ⟨u, hu⟩ : ↥(UH153 T M V₁ Mc)) : G) := by simp
    rw [e]
    exact W.mul_mem hwW (hZW hZ)

omit [Finite G] in
theorem tildeOf_Z_eq_bot (Z : Subgroup G) : tildeOf Z Z = ⊥ := by
  ext y
  rw [Subgroup.mem_bot]
  constructor
  · intro hy
    obtain ⟨x, hxZ, rfl⟩ := mem_secImg.1 hy
    exact secMk_eq_one_iff.2 hxZ
  · rintro rfl
    exact one_mem _

theorem card_tilde_eq (cx : Ctx15350 T Mc M V₁ V₂ t) :
    Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) =
      (quasithinOmegaOneCenter T).relIndex (UH153 T M V₁ Mc) := by
  have h := relIndex_secImg (A := NZ T) (B := quasithinOmegaOneCenter T) (T := quasithinOmegaOneCenter T)
    (H := UH153 T M V₁ Mc) le_rfl ((S153E.Z_le_ZS cx).trans (S153E.ZS_le_U cx)) (U_le_NZ cx)
  have hbot : secImg (NZ T) (quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = ⊥ :=
    tildeOf_Z_eq_bot _
  rw [hbot, Subgroup.relIndex_bot_left] at h
  exact h

theorem card_tilde (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) = 2 ^ (2 * (s + 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_tilde_eq cx]
  obtain ⟨n, hn⟩ := cx.hF.isPGroup_conjClosure.exists_card_eq
  have hmul := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)
  have hdvd : (quasithinOmegaOneCenter T).relIndex (UH153 T M V₁ Mc) ∣ 2 ^ n := by
    rw [← hn, ← hmul]
    exact Dvd.intro _ rfl
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hrank := c.h56.rank
  rw [mIdx, hk, padicValNat.prime_pow] at hrank
  rw [hk, hrank]

theorem card_comm_Vs_le (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(commIn153 (XStar153 T M V₁ Mc (VZ T M))
      (⊤ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))) ≤ 4 := by
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
  have hZP : quasithinOmegaOneCenter T ≤ P := by
    rw [← hVU]
    exact le_inf cx.c.hyp.Z_le_VZ ((S153E.Z_le_ZS cx).trans (S153E.ZS_le_U cx))
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
  let Pt : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
    (tildeOf (quasithinOmegaOneCenter T) P).subgroupOf
      (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))
  have hle : commIn153 (XStar153 T M V₁ Mc (VZ T M))
      (⊤ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) ≤ Pt := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨a, ha, w, -, rfl⟩
    obtain ⟨n, hnV, rfl⟩ := (mem_XStar_iff cx _ _).1 ha
    obtain ⟨u, rfl⟩ := piU_surjective cx w
    have hmemP : (n : G) * u * (n : G)⁻¹ * (u : G)⁻¹ ∈ P := by
      have h1 : ⁅(n : G), (u : G)⁆ ∈ ⁅VZ T M, UH153 T M V₁ Mc⁆ :=
        Subgroup.commutator_mem_commutator hnV u.2
      rw [Subgroup.commutator_comm, hUV] at h1
      exact h1
    rw [← piU_conj cx n (NZ_le_Mc cx n.2) u, ← map_inv, ← map_mul]
    show ((piU cx _ : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
      SecQuot (NZ T) (quasithinOmegaOneCenter T)) ∈ tildeOf (quasithinOmegaOneCenter T) P
    rw [piU_coe]
    exact secMk_mem_secImg (A := NZ T) (B := quasithinOmegaOneCenter T) (X := P)
      (x := ⟨_, U_le_NZ cx (Subgroup.mul_mem _ (S153E.U_conj_mem (NZ_le_Mc cx n.2) u.2)
        (Subgroup.inv_mem _ u.2))⟩) (by simpa using hmemP)
  calc Nat.card ↥(commIn153 (XStar153 T M V₁ Mc (VZ T M))
        (⊤ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))) ≤
        Nat.card ↥Pt := Subgroup.card_le_of_le hle
    _ = Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) P) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv
    _ = 4 := h4

end Main

end S153E57

namespace S153E

theorem lemma_15_3_57 {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
    (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}
    {y t₁ : G} (c : Chain15356 cx N₁ N₂ g s y t₁) : Concl15357 cx s := by
  refine ⟨S153E57.one_ne_of cx c.h52, S153E57.one_irr_of cx c, ?_⟩
  intro Kst _ _ _ hKnorm hrank
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
    commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  have hq : ∀ q : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)), q * q = 1 := by
    intro q
    have := cx.hF.isElemAbelian_tilde.2 q q.2
    exact Subtype.ext (by simpa [pow_two] using this)
  obtain ⟨v, hvV, hv1, hvuniq⟩ := S153E57.exists_v c
  obtain ⟨z₀, hz₀⟩ := S153E57.exists_z₀ cx
  obtain ⟨zS, hzS, hzSZ⟩ := S153E57.exists_zS_aux cx
  have hzSU : zS ∈ UH153 T M V₁ Mc := ZS_le_U cx hzS
  have hcore : S153E57.Core (HStar153 T M V₁ Mc) Kst (XStar153 T M V₁ Mc (VZ T M))
      (S153E57.XS T M V₁ Mc y ⊔ S153E57.XS' T M V₁ Mc y t₁)
      (Subgroup.zpowers (S153E57.ttOf cx c.ht₁.1)) v z₀ :=
    { nontriv := ⟨⟨S153E57.piU cx ⟨zS, hzSU⟩, 1,
        fun h => hzSZ ((S153E57.piU_eq_one_iff cx _).1 h)⟩⟩
      sq := hq
      irr_H := S153E57.irr_H cx c
      normal := hKnorm
      rank := hrank
      v_mem := hvV
      v_ne := hv1
      V_two := hvuniq
      V_le := S153E57.XStar_le_HStar cx cx.hF.V_le_H
      comm_le := S153E57.card_comm_Vs_le cx c
      P₁_two := S153E57.isPGroup_A cx c
      P₂_two := S153E57.isPGroup_zpowers_tt cx c.ht₁.1
      P₂_norm := fun p hp a ha => (Subgroup.mem_normalizer_iff.1
        (Subgroup.zpowers_le.2 (S153E57.tt_mem_normalizer cx c) hp) a).1 ha
      P₁_le := S153E57.A_le_HStar cx c
      P₂_le := Subgroup.zpowers_le.2 (S153E57.tt_mem_HStar cx c.ht₁.1)
      P₁_comm := S153E57.A_comm_v c hvV
      P₂_comm := fun d hd => by
        have hcomm := S153E57.tt_comm_v c hvV hv1 hvuniq
        have : Subgroup.zpowers (S153E57.ttOf cx c.ht₁.1) ≤
            Subgroup.centralizer ({v} : Set (MulAut _)) := by
          refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
          rw [Set.mem_singleton_iff.1 hh]
          exact hcomm.symm
        exact (Subgroup.mem_centralizer_iff.1 (this hd) v (Set.mem_singleton v)).symm
      fixed := fun x hA ht => S153E57.fixed_cases cx c z₀ hz₀ x
        (fun d hd => hA d (Subgroup.mem_sup_left hd)) (ht _ (Subgroup.mem_zpowers _)) }
  exact ⟨hcore.comm_ne_bot, hcore.dichotomy s (S153E57.card_tilde cx c)⟩

end S153E

end CFSG.Quasithin
