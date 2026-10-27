module

public import CFSG.Quasithin.EmptyFaithful.S153E57E
public import CFSG.Quasithin.EmptyFaithful.S153E57A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E57

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem U_le_NZ (cx : Ctx15350 T Mc M V₁ V₂ t) : UH153 T M V₁ Mc ≤ NZ T :=
  fun _ hu => Mc_le_NZ cx (pCoreOf_le 2 Mc (S153E.U_le_Q cx hu))

@[expose] noncomputable def piU (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ↥(UH153 T M V₁ Mc) →* ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
  MonoidHom.codRestrict
    ((secMk (NZ T) (quasithinOmegaOneCenter T)).comp (Subgroup.inclusion (U_le_NZ cx)))
    _ (fun u => secMk_mem_secImg u.2)

theorem piU_coe (cx : Ctx15350 T Mc M V₁ V₂ t) (u : ↥(UH153 T M V₁ Mc)) :
    ((piU cx u : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
      SecQuot (NZ T) (quasithinOmegaOneCenter T)) =
      secMk (NZ T) (quasithinOmegaOneCenter T) ⟨u, U_le_NZ cx u.2⟩ := rfl

theorem piU_surjective (cx : Ctx15350 T Mc M V₁ V₂ t) : Function.Surjective (piU cx) := by
  intro x
  obtain ⟨u, huU, hux⟩ := mem_secImg.1 x.2
  exact ⟨⟨u, huU⟩, Subtype.ext hux⟩

theorem piU_eq_one_iff (cx : Ctx15350 T Mc M V₁ V₂ t) (u : ↥(UH153 T M V₁ Mc)) :
    piU cx u = 1 ↔ (u : G) ∈ quasithinOmegaOneCenter T := by
  rw [← secMk_eq_one_iff (A := NZ T) (B := quasithinOmegaOneCenter T) (x := ⟨u, U_le_NZ cx u.2⟩)]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem piU_conj (cx : Ctx15350 T Mc M V₁ V₂ t) (n : NZ T) (hn : (n : G) ∈ Mc)
    (u : ↥(UH153 T M V₁ Mc)) :
    piU cx ⟨(n : G) * u * (n : G)⁻¹, S153E.U_conj_mem hn u.2⟩ = rho cx n (piU cx u) := by
  apply Subtype.ext
  rw [rho_apply_coe]
  change secMk (NZ T) (quasithinOmegaOneCenter T) ⟨(n : G) * u * (n : G)⁻¹, _⟩ = _
  have : (⟨(n : G) * u * (n : G)⁻¹, U_le_NZ cx (S153E.U_conj_mem hn u.2)⟩ : NZ T) =
      n * ⟨u, U_le_NZ cx u.2⟩ * n⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv]
  rfl

theorem exists_z₀ (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ∃ z₀ : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)),
      ∀ u : ↥(UH153 T M V₁ Mc), (u : G) ∈ ZS153 T M V₁ → piU cx u = 1 ∨ piU cx u = z₀ := by
  obtain ⟨zS, hzS, hzSZ⟩ := exists_zS_aux cx
  have hzSU : zS ∈ UH153 T M V₁ Mc := S153E.ZS_le_U cx hzS
  refine ⟨piU cx ⟨zS, hzSU⟩, fun u hu => ?_⟩
  by_cases hZ : (u : G) ∈ quasithinOmegaOneCenter T
  · exact Or.inl ((piU_eq_one_iff cx u).2 hZ)
  · right
    have hidx : ((quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁)).index = 2 := by
      have hmul := Subgroup.card_mul_index ((quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁))
      have hc : Nat.card ↥((quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁)) = 2 := by
        rw [← Z_card cx]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S153E.Z_le_ZS cx)).toEquiv
      rw [hc, Decomp153.card_ZS cx.c.hyp cx.c.decomp] at hmul
      omega
    have hmem : (⟨u, hu⟩ : ↥(ZS153 T M V₁))⁻¹ * ⟨zS, hzS⟩ ∈
        (quasithinOmegaOneCenter T).subgroupOf (ZS153 T M V₁) := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      constructor
      · intro h
        exact absurd (by simpa [Subgroup.mem_subgroupOf] using h) hZ
      · intro h
        exact absurd (by simpa [Subgroup.mem_subgroupOf] using h) hzSZ
    have hZ' : (u : G)⁻¹ * zS ∈ quasithinOmegaOneCenter T := by
      simpa [Subgroup.mem_subgroupOf] using hmem
    have h1 : piU cx (u⁻¹ * ⟨zS, hzSU⟩) = 1 := (piU_eq_one_iff cx _).2 (by simpa using hZ')
    rw [map_mul, map_inv] at h1
    exact inv_mul_eq_one.1 h1

theorem fixed_cases (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁)
    (z₀ : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))
    (hz₀ : ∀ u : ↥(UH153 T M V₁ Mc), (u : G) ∈ ZS153 T M V₁ → piU cx u = 1 ∨ piU cx u = z₀)
    (x : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))
    (hA : ∀ d ∈ XS T M V₁ Mc y, d x = x) (htt : ttOf cx c.ht₁.1 x = x) : x = 1 ∨ x = z₀ := by
  obtain ⟨u, huZS, hux⟩ := fixed_imp cx c x hA htt
  have huU : (u : G) ∈ UH153 T M V₁ Mc := S153E.ZS_le_U cx huZS
  have hpi : piU cx ⟨u, huU⟩ = x := Subtype.ext hux
  rcases hz₀ ⟨u, huU⟩ huZS with h | h
  · left
    rw [← hpi]
    exact h
  · right
    rw [← hpi]
    exact h

theorem X'_le_Mc (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁) :
    conjSubgroup (Xgp153 T M V₁ Mc y) t₁ ≤ Mc := by
  intro n hn
  have hX := X_le_Mc cx c.hy.1 c.h56.V0_eq (mem_conjSubgroup_iff.1 hn)
  have ht : t₁ ∈ Mc := S153E.T_le_Mc cx c.ht₁.1
  have e : n = t₁⁻¹ * (t₁ * n * t₁⁻¹) * t₁ := by group
  rw [e]
  exact Mc.mul_mem (Mc.mul_mem (Mc.inv_mem ht) hX) ht

theorem A_le_HStar (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁) :
    XS T M V₁ Mc y ⊔ XS' T M V₁ Mc y t₁ ≤ HStar153 T M V₁ Mc :=
  sup_le (XStar_le_HStar cx (X_le_Mc cx c.hy.1 c.h56.V0_eq)) (XStar_le_HStar cx (X'_le_Mc cx c))

theorem tt_mem_HStar (cx : Ctx15350 T Mc M V₁ V₂ t) (ht₁ : t₁ ∈ T) :
    ttOf cx ht₁ ∈ HStar153 T M V₁ Mc :=
  rho_mem_XStar (B := Mc) cx _ (S153E.T_le_Mc cx ht₁)

theorem irr_H (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15356 cx N₁ N₂ g s y t₁) :
    IsIrrOn153 (HStar153 T M V₁ Mc)
      (⊤ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) := by
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
    commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  have hq : ∀ q : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)), q * q = 1 := by
    intro q
    have := cx.hF.isElemAbelian_tilde.2 q q.2
    exact Subtype.ext (by simpa [pow_two] using this)
  obtain ⟨z₀, hz₀⟩ := exists_z₀ cx
  refine ⟨?_, fun _ _ _ _ => Subgroup.mem_top _, fun B _ hB => ?_⟩
  · intro h
    obtain ⟨zS, hzS, hzSZ⟩ := exists_zS_aux cx
    have hzSU : zS ∈ UH153 T M V₁ Mc := S153E.ZS_le_U cx hzS
    have hmem : piU cx ⟨zS, hzSU⟩ ∈ (⊤ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T)
        (UH153 T M V₁ Mc))) := Subgroup.mem_top _
    rw [h, Subgroup.mem_bot] at hmem
    exact hzSZ ((piU_eq_one_iff cx _).1 hmem)
  · by_cases hBbot : B = ⊥
    · exact Or.inl hBbot
    · right
      have hHA := A_le_HStar cx c
      have htt := tt_mem_HStar cx c.ht₁.1
      obtain ⟨x, hxB, hx1, hxA, hxtt⟩ := exists_fixed_two
        (S₁ := XS T M V₁ Mc y ⊔ XS' T M V₁ Mc y t₁)
        (S₂ := Subgroup.zpowers (ttOf cx c.ht₁.1)) (isPGroup_A cx c)
        (isPGroup_zpowers_tt cx c.ht₁.1)
        (fun p hp a ha => (Subgroup.mem_normalizer_iff.1
          (Subgroup.zpowers_le.2 (tt_mem_normalizer cx c) hp) a).1 ha)
        (B := B) (fun s hs b hb => hB s (hHA hs) b hb)
        (fun s hs b hb => hB s (Subgroup.zpowers_le.2 htt hs) b hb) hBbot
        (isPGroup_two_of_mul_self hq B)
      have hxz : x = z₀ :=
        (fixed_cases cx c z₀ hz₀ x (fun d hd => hxA d (Subgroup.mem_sup_left hd))
          (hxtt _ (Subgroup.mem_zpowers _))).resolve_left hx1
      have hz₀B : z₀ ∈ B := hxz ▸ hxB
      let W : Subgroup G := (B.comap (piU cx)).map (UH153 T M V₁ Mc).subtype
      have hZS : ∀ z ∈ ZS153 T M V₁, ∀ hzU : z ∈ UH153 T M V₁ Mc, piU cx ⟨z, hzU⟩ ∈ B := by
        intro z hz hzU
        rcases hz₀ ⟨z, hzU⟩ hz with h | h
        · rw [h]
          exact B.one_mem
        · rw [h]
          exact hz₀B
      have hUW : UH153 T M V₁ Mc ≤ W := by
        refine conjClosure_le fun k hk z hz => ?_
        have hkU : k * z * k⁻¹ ∈ UH153 T M V₁ Mc :=
          S153E.U_conj_mem hk (S153E.ZS_le_U cx hz)
        refine Subgroup.mem_map.2 ⟨⟨k * z * k⁻¹, hkU⟩, ?_, rfl⟩
        rw [Subgroup.mem_comap]
        have e := piU_conj cx ⟨k, Mc_le_NZ cx hk⟩ hk ⟨z, S153E.ZS_le_U cx hz⟩
        rw [show (⟨(⟨k, Mc_le_NZ cx hk⟩ : NZ T) * (⟨z, S153E.ZS_le_U cx hz⟩ : ↥(UH153 T M V₁ Mc)) *
            ((⟨k, Mc_le_NZ cx hk⟩ : NZ T) : G)⁻¹, S153E.U_conj_mem hk (S153E.ZS_le_U cx hz)⟩ :
            ↥(UH153 T M V₁ Mc)) = ⟨k * z * k⁻¹, hkU⟩ from rfl] at e
        rw [e]
        exact hB _ (rho_mem_XStar (B := Mc) cx ⟨k, Mc_le_NZ cx hk⟩ hk) _
          (hZS z hz (S153E.ZS_le_U cx hz))
      rw [eq_top_iff]
      intro x' _
      obtain ⟨u, rfl⟩ := piU_surjective cx x'
      obtain ⟨u', hu', hu'u⟩ := Subgroup.mem_map.1 (hUW u.2)
      have : u' = u := Subtype.ext hu'u
      rw [Subgroup.mem_comap] at hu'
      rwa [this] at hu'

end Main

end S153E57

end CFSG.Quasithin
