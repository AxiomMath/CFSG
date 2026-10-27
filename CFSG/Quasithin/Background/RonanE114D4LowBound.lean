module

public import CFSG.Quasithin.Background.RonanE114D4LowThm
public import CFSG.Quasithin.Background.RonanE114D4LowSetup
public import CFSG.Quasithin.Background.RonanE114D4LowE
public import CFSG.Quasithin.Background.RonanE114D4Clause
public import CFSG.Quasithin.Background.RonanE114O2
public import CFSG.Quasithin.Vol2.RonanE114Lower

public section

namespace CFSG.Quasithin.RonanE114Low

open CFSG.GH74.BNPair CFSG.Quasithin CFSG.Quasithin.H13.F431.BN CFSG.Open
  CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage4.Hex CFSG.Timmesfeld.RankTwo
  CFSG.LieType.Steinberg.TwistedD4

theorem isElemAbelian_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {H : Subgroup X}
    (hH : IsElemAbelian 2 H) : IsElemAbelian 2 (H.map f) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨b, hb, hby⟩ := y.2
    have h := congrArg Subtype.val (hH.1.is_comm.comm (⟨a, ha⟩ : H) ⟨b, hb⟩)
    simp only [Subgroup.coe_mul] at h ⊢
    rw [← hax, ← hby, ← map_mul, h, map_mul]
  · obtain ⟨a, ha, rfl⟩ := hx
    rw [← map_pow, hH.2 a ha, map_one]

section Coords

variable {X : Type} [Group X] {K : Type} [Field K] [CharP K 2] {σ : K →+* K}
  {hσ : ∀ c, σ (σ (σ c)) = c} {D : RankTwoSystem X 6} {ψ : ∀ i : Fin 6, d43Par σ i → X}
  (hψ : D4Coords D hσ ψ)
include hψ

theorem isElemAbelian_root_three : IsElemAbelian 2 (D.root 3) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨s, hs⟩ := exists_psi2 hψ x.2
    obtain ⟨t, ht⟩ := exists_psi2 hψ y.2
    simp only [Subgroup.coe_mul]
    rw [← hs, ← ht]
    have h1 := hψ.rel.add 2 s t
    have h2 := hψ.rel.add 2 t s
    have h3 : ((s : d43Par σ 2) + (t : d43Par σ 2) : d43Par σ 2) =
        (t : d43Par σ 2) + (s : d43Par σ 2) := add_comm _ _
    calc ψ 2 s * ψ 2 t = ψ 2 ((s : d43Par σ 2) + (t : d43Par σ 2)) := h1.symm
      _ = ψ 2 ((t : d43Par σ 2) + (s : d43Par σ 2)) := congrArg (ψ 2) h3
      _ = ψ 2 t * ψ 2 s := h2
  · obtain ⟨t, rfl⟩ := exists_psi2 hψ hx
    rw [pow_two]
    exact psi_two_mul_self hψ t

theorem card_root_three : Nat.card (D.root 3) = Nat.card K := by
  refine (Nat.card_congr (Equiv.ofBijective (fun t : K => (⟨ψ 2 t, hψ.mem 2 t⟩ : D.root 3))
    ⟨fun a b hab => hψ.inj 2 (congrArg Subtype.val hab), fun y => ?_⟩)).symm
  obtain ⟨t, ht⟩ := exists_psi2 hψ y.2
  exact ⟨t, Subtype.ext ht⟩

end Coords

theorem root_one_eq_conj {X : Type} [Group X] (D : RankTwoSystem X 6) :
    D.root 1 = (D.root 3).map (MulAut.conj (mi D true * mi D false)⁻¹).toMonoidHom := by
  ext y
  constructor
  · intro hy
    have h1 := conj_mi_false D (k := 1) (by norm_num) (by norm_num) hy
    have h1' : mi D false * y * (mi D false)⁻¹ ∈ D.root 5 := by simpa using h1
    have h2 := conj_mi_true D (k := 5) (by norm_num) (by norm_num) h1'
    have h2' : mi D true * (mi D false * y * (mi D false)⁻¹) * (mi D true)⁻¹ ∈ D.root 3 := by
      simpa using h2
    refine ⟨_, h2', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨x, hx, rfl⟩
    have h1 := conj_mi_true_inv D (k := 3) (by norm_num) (by norm_num) hx
    have h1' : (mi D true)⁻¹ * x * mi D true ∈ D.root 5 := by simpa using h1
    have h2 := conj_mi_false_inv D (k := 5) (by norm_num) (by norm_num) h1'
    have h2' : (mi D false)⁻¹ * ((mi D true)⁻¹ * x * mi D true) * mi D false ∈ D.root 1 := by
      simpa using h2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    convert h2' using 1
    group

section Transport

variable {G : Type} [Group G] {L : Subgroup G} [L.Normal] {X : Type} [Group X] (φ : ↥L ≃* X)

@[expose] def emb : X →* G := L.subtype.comp φ.symm.toMonoidHom

theorem emb_injective : Function.Injective (emb φ) :=
  L.subtype_injective.comp φ.symm.injective

theorem emb_mem (x : X) : emb φ x ∈ L := (φ.symm x).2

theorem map_emb_le (H : Subgroup X) : H.map (emb φ) ≤ L := by
  rintro _ ⟨x, -, rfl⟩
  exact emb_mem φ x

theorem map_comap_emb {H : Subgroup G} (h : H ≤ L) : (H.comap (emb φ)).map (emb φ) = H := by
  refine le_antisymm (Subgroup.map_comap_le _ _) fun x hx => ?_
  refine ⟨φ ⟨x, h hx⟩, ?_, ?_⟩
  · show emb φ (φ ⟨x, h hx⟩) ∈ H
    simp [emb, hx]
  · simp [emb]

theorem emb_conjAut (g : G) (x : X) :
    emb φ (RonanE114.conjAut φ g x) = g * emb φ x * g⁻¹ :=
  RonanE114.coe_symm_conjAut φ g x

theorem conjAut_emb (x : X) : RonanE114.conjAut φ (emb φ x) = MulAut.conj x := by
  ext y
  apply emb_injective φ
  rw [emb_conjAut]
  simp [emb, MulAut.conj_apply]

theorem map_emb_conjAut (g : G) (H : Subgroup X) :
    (H.map (RonanE114.conjAut φ g).toMonoidHom).map (emb φ) = A1b.conjSub g (H.map (emb φ)) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨emb φ y, ⟨y, hy, rfl⟩, ?_⟩
    simp [emb_conjAut, MulAut.conj_apply]
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨RonanE114.conjAut φ g y, ⟨y, hy, rfl⟩, ?_⟩
    simp [emb_conjAut, MulAut.conj_apply]

theorem mem_normalizer_map_emb_iff (g : G) (H : Subgroup X) :
    g ∈ Subgroup.normalizer ((H.map (emb φ) : Subgroup G) : Set G) ↔
      H.map (RonanE114.conjAut φ g).toMonoidHom = H := by
  rw [← A1b.conjSub_eq_iff_mem_normalizer, ← map_emb_conjAut]
  exact (Subgroup.map_injective (emb_injective φ)).eq_iff

end Transport

theorem pCoreOf_le_of_isSylowIn {G : Type*} [Group G] [Finite G] {S H : Subgroup G}
    (hS : IsSylowIn 2 S H) : pCoreOf 2 H ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let P : Sylow 2 H := hS'.toSylow hS.2.2
  have : (CFSG.Open.pCore 2 H).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have h1 : CFSG.Open.pCore 2 H ≤ (P : Subgroup H) :=
    IsPGroup.le_sylow_of_normal (CFSG.LieType.BorelTits.pCore_isPGroup 2) P
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  have h3 : (P : Subgroup H).map H.subtype = S := by
    change (S.subgroupOf H).map H.subtype = S
    rw [Subgroup.map_subgroupOf_eq_of_le hS.1]
  change Subgroup.map H.subtype (CFSG.Open.pCore 2 H) ≤ S
  rw [← h3]
  exact h2

theorem conjSub_weakClosure_le {G : Type*} [Group G] {T L : Subgroup G}
    {Ω : Set (Subgroup G)} {h : G} (hΩ : ∀ B ∈ Ω, A1b.conjSub h B ∈ Ω)
    (hΩL : ∀ B ∈ Ω, B ≤ L) (hTL : A1b.conjSub h (T ⊓ L) = T ⊓ L) :
    A1b.conjSub h (E1.weakClosure T Ω) ≤ E1.weakClosure T Ω := by
  rw [A1b.conjSub, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun B hB => iSup_le fun hBT => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hle : A1b.conjSub h B ≤ T := by
    have h1 : A1b.conjSub h B ≤ A1b.conjSub h (T ⊓ L) := A1b.conjSub_mono h (le_inf hBT (hΩL B hB))
    rw [hTL] at h1
    exact h1.trans inf_le_left
  exact le_iSup₂_of_le (A1b.conjSub h B) (hΩ B hB) (le_iSup_of_le hle le_rfl)

section Lower


theorem three_mul_le_nParam {G : Type} [Group G] [Finite G] {L T : Subgroup G} [L.Normal]
    (hT : IsSylowIn 2 T ⊤) {n : ℕ} (hn : 1 ≤ n) (hL : Is3D4 2 n ↥L) :
    ((3 * n : ℕ) : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, _, _, K, _, _, σ, hσ, D, ψ, hψ, hU, hσ1, hBT, hK, φ, hφU⟩ := exists_model_data hT hL
  have hιinj := emb_injective φ
  have hLN : ∀ H : Subgroup G, H ≤ Subgroup.normalizer (L : Set G) := fun H => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hTL : D.U.map (emb φ) = T ⊓ L := by
    rw [← hφU, Subgroup.map_map]
    have : (emb φ).comp φ.toMonoidHom = L.subtype := by
      ext x
      simp [emb]
    rw [this, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  have hmemU : ∀ z : X, emb φ z ∈ T → z ∈ D.U := by
    intro z hz
    have h3 : emb φ z ∈ T ⊓ L := ⟨hz, emb_mem φ z⟩
    rw [← hTL] at h3
    obtain ⟨u, hu, hue⟩ := h3
    rw [← hιinj hue]
    exact hu
  set A₀ : Subgroup G := (D.root 3).map (emb φ) with hA₀
  have hA₀elem : IsElemAbelian 2 A₀ := isElemAbelian_map _ (isElemAbelian_root_three hψ)
  set Pb : Subgroup G := Subgroup.normalizer (((P D false).map (emb φ) : Subgroup G) : Set G)
    with hPb
  have hcardA : ∀ α : MulAut X,
      Nat.card (((D.root 3).map α.toMonoidHom).map (emb φ)) = 2 ^ (3 * n) := by
    intro α
    rw [Subgroup.card_map_of_injective hιinj, Subgroup.card_map_of_injective α.injective,
      card_root_three hψ, hK]
  have h3n : 2 ≤ 3 * n := by omega
  refine Vol2.Ch11.SecE3.Lie3.le_nParam_of_forall_isE_le (A := A₀) (P := Pb) h3n hT ?_
    hA₀elem ?_ ?_
  ·
    intro htop
    apply P_ne_top D false
    rw [eq_top_iff]
    intro x _
    have hx : emb φ x ∈ Pb := htop ▸ Subgroup.mem_top _
    rw [hPb, mem_normalizer_map_emb_iff, conjAut_emb] at hx
    rw [← stab_v D false, ← normalizer_stab D hU (v D false)]
    exact mem_normalizer_of_map_conj (by rwa [stab_v])
  ·
    intro g hgT Kg hKg
    set α : MulAut X := RonanE114.conjAut φ g with hα
    set A' : Subgroup X := (D.root 3).map α.toMonoidHom with hA'
    have hAeq : A1b.conjSub g A₀ = A'.map (emb φ) := by
      rw [hA', map_emb_conjAut]
    have hAelem : IsElemAbelian 2 (A1b.conjSub g A₀) := by
      rw [hAeq]
      exact isElemAbelian_map _ (isElemAbelian_map _ (isElemAbelian_root_three hψ))
    have hAcard : Nat.card (A1b.conjSub g A₀) = 2 ^ (3 * n) := by
      rw [hAeq]
      exact hcardA α
    obtain ⟨hAK, hcard⟩ := E3.card_le_of_isE hT hgT hAelem hKg
    have hAL : A1b.conjSub g A₀ ≤ L := by
      rw [hAeq]
      exact map_emb_le φ _
    have hlt : 2 ^ (3 * n - 1) < 2 ^ (3 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hne : A1b.conjSub g A₀ ⊓ pCoreOf 2 Kg ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot, mul_one, hAcard] at hcard
      omega
    set Φ : Subgroup (MulAut X) := Kg.map (RonanE114.conjAut φ) with hΦ
    set K₁ : Subgroup X := Kg.comap (emb φ) with hK₁
    have hK₁map : K₁.map (emb φ) = Kg ⊓ L := by
      rw [hK₁, ← map_comap_emb φ (inf_le_right : Kg ⊓ L ≤ L)]
      congr 1
      ext x
      simp [emb_mem]
    set R₀ : Subgroup X := (pCoreOf 2 Kg ⊓ L).comap (emb φ) with hR₀def
    have hR₀map : R₀.map (emb φ) = pCoreOf 2 Kg ⊓ L := map_comap_emb φ inf_le_right
    have hR₀ : R₀ ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro z hz
      have hz' : z ∈ pCoreOf 2 Kg ⊓ L :=
        Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hz).2, hAL (Subgroup.mem_inf.1 hz).1⟩
      rw [← hR₀map, h, Subgroup.map_bot] at hz'
      exact hz'
    have hR₀2 : IsPGroup 2 R₀ :=
      ((pCoreOf_isPGroup 2 Kg).to_le inf_le_left).comap_of_injective _ hιinj
    have hΦR₀ : ∀ φ' ∈ Φ, R₀.map φ'.toMonoidHom = R₀ := by
      rintro _ ⟨k, hk, rfl⟩
      apply Subgroup.map_injective hιinj
      rw [map_emb_conjAut, hR₀map, A1b.conjSub_eq_iff_mem_normalizer]
      have h1 := le_normalizer_pCoreOf 2 Kg hk
      have h2 := hLN Kg hk
      rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
      intro z
      simp only [Subgroup.mem_inf]
      exact and_congr (h1 z) (h2 z)
    have hK₁Φ : ∀ x ∈ K₁, MulAut.conj x ∈ Φ := fun x hx => ⟨emb φ x, hx, conjAut_emb φ x⟩
    have hAK₁ : A' ≤ K₁ := fun x hx => hAK (by rw [hAeq]; exact ⟨x, hx, rfl⟩)
    have hO2map : (pCoreOf 2 K₁).map (emb φ) ≤ pCoreOf 2 Kg := by
      rw [map_pCoreOf_of_injective _ hιinj, hK₁map]
      exact pCoreOf_inf_le (hLN Kg)
    have hO2 : ¬ A' ≤ pCoreOf 2 K₁ := by
      intro h
      refine RonanE114.not_isE_of_le_pCoreOf ?_ hKg
      rw [hAeq]
      exact (Subgroup.map_mono h).trans hO2map
    have hOinf : A' ⊓ (CFSG.solvableRadical ↥K₁).map K₁.subtype ≠ ⊥ := by
      intro h
      refine not_isE_of_inf_solvableRadical hAK ?_ (by rw [hAcard]; exact hlt) hKg
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzA, hzR⟩ := Subgroup.mem_inf.1 hz
      have hz1 : z ∈ (CFSG.solvableRadical ↥(Kg ⊓ L)).map (Kg ⊓ L).subtype :=
        solvableRadical_inf_le (hLN Kg) (Subgroup.mem_inf.2 ⟨hzR, hAL hzA⟩)
      rw [← hK₁map, ← map_solvableRadical_of_injective _ hιinj] at hz1
      rw [hAeq] at hzA
      have hz2 : z ∈ (A' ⊓ (CFSG.solvableRadical ↥K₁).map K₁.subtype).map (emb φ) := by
        rw [Subgroup.map_inf_eq _ _ _ hιinj]
        exact Subgroup.mem_inf.2 ⟨hzA, hz1⟩
      rw [h, Subgroup.map_bot] at hz2
      exact hz2
    have hO2U : pCoreOf 2 K₁ ≤ D.U := by
      intro z hz
      have h1 : emb φ z ∈ pCoreOf 2 Kg := hO2map ⟨z, hz, rfl⟩
      exact hmemU z (Subgroup.mem_inf.1 (pCoreOf_le_of_isSylowIn hKg.2.2.1 h1)).1
    have hfix := fix_line hU hψ hσ1 hBT Φ K₁ hK₁Φ hR₀ hR₀2 hΦR₀ α hAK₁ hO2 hOinf hO2U
    intro k hk
    rw [hPb, mem_normalizer_map_emb_iff]
    exact hfix _ ⟨k, hk, rfl⟩
  ·
    intro g hg
    set Ω : Set (Subgroup G) := {B | ∃ g : G, B = A1b.conjSub g A₀} with hΩ
    set W := E1.weakClosure T Ω with hW
    have hΩL : ∀ B ∈ Ω, B ≤ L := by
      rintro _ ⟨g', rfl⟩
      rw [hA₀, ← map_emb_conjAut]
      exact map_emb_le φ _
    have hΩc : ∀ (h : G), ∀ B ∈ Ω, A1b.conjSub h B ∈ Ω := by
      rintro h _ ⟨g', rfl⟩
      exact ⟨h * g', by rw [A1b.conjSub_mul]⟩
    have hWL : W ≤ L := iSup₂_le fun B hB => iSup_le fun _ => hΩL B hB
    have hWT : W ≤ T := iSup₂_le fun B _ => iSup_le fun hBT => hBT
    set W₁ := W.comap (emb φ) with hW₁
    have hW₁map : W₁.map (emb φ) = W := map_comap_emb φ hWL
    have hW₁U : W₁ ≤ D.U := fun z hz => hmemU z (hWT hz)
    have hX1 : D.root 1 ≤ W₁ := by
      have hmem : (D.root 1).map (emb φ) ∈ Ω := by
        refine ⟨emb φ (mi D true * mi D false)⁻¹, ?_⟩
        rw [root_one_eq_conj D, ← conjAut_emb φ, map_emb_conjAut]
      have hle : (D.root 1).map (emb φ) ≤ T := by
        have := Subgroup.map_mono (f := emb φ) (D.root_le_U (k := 1) le_rfl (by norm_num))
        rw [hTL] at this
        exact this.trans inf_le_left
      have hW' : (D.root 1).map (emb φ) ≤ W :=
        le_iSup₂_of_le ((D.root 1).map (emb φ)) hmem (le_iSup_of_le hle le_rfl)
      intro x hx
      exact hW' ⟨x, hx, rfl⟩
    have hBW : D.B ≤ Subgroup.normalizer (W₁ : Set X) := by
      intro b hb
      have hTLb : ∀ c ∈ D.B, A1b.conjSub (emb φ c) (T ⊓ L) = T ⊓ L := by
        intro c hc
        rw [← hTL, ← map_emb_conjAut, conjAut_emb]
        congr 1
        have hcU : c ∈ Subgroup.normalizer (D.U : Set X) := by
          rw [normalizer_U_eq_B]
          exact hc
        rw [← A1b.conjSub_eq_iff_mem_normalizer] at hcU
        exact hcU
      have h1 := conjSub_weakClosure_le (hΩc (emb φ b)) hΩL (hTLb b hb)
      have h2 := conjSub_weakClosure_le (hΩc (emb φ b⁻¹)) hΩL (hTLb b⁻¹ (D.B.inv_mem hb))
      have key : emb φ b ∈ Subgroup.normalizer (W : Set G) := by
        rw [← A1b.conjSub_eq_iff_mem_normalizer]
        refine le_antisymm h1 ?_
        have h3 := A1b.conjSub_mono (emb φ b) h2
        rw [← A1b.conjSub_mul, map_inv, mul_inv_cancel, A1b.conjSub_one] at h3
        exact h3
      rw [← hW₁map, mem_normalizer_map_emb_iff, conjAut_emb] at key
      exact mem_normalizer_of_map_conj key
    have hgW : W₁.map (RonanE114.conjAut φ g).toMonoidHom = W₁ := by
      rw [← mem_normalizer_map_emb_iff, hW₁map]
      exact hg
    rw [hPb, mem_normalizer_map_emb_iff]
    exact map_P_false_of_map_weakClosure hU hψ hσ1 hW₁U hX1 hBW _ hgW

theorem e_1_14_two_printed_local :
    ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
      IsSimpleGroup ↥(CFSG.generalizedFitting G) → IsSylowIn 2 T ⊤ →
      CFSG.generalizedFitting G ⊔ T = ⊤ →
        ∀ n : ℕ, 1 ≤ n → Is3D4 2 n ↥(CFSG.generalizedFitting G) →
          E1.nParam (⊤ : Subgroup G) = ((3 * n : ℕ) : ℕ∞) := by
  intro G _ _ T _ _ hT hFT n hn hL
  haveI : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  exact le_antisymm (RonanE114.clause_two_le hT hFT hn hL) (three_mul_le_nParam hT hn hL)

end Lower

end CFSG.Quasithin.RonanE114Low
