module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3Frame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

namespace L3Frame

variable {Γ Γ' : Type} [Group Γ] [Group Γ'] {p : ℕ} {k : Type} [Field k]

theorem comm_iff (Ψ : Γ ≃* Γ') {g h : Γ} : g * h = h * g ↔ Ψ g * Ψ h = Ψ h * Ψ g := by
  rw [← map_mul, ← map_mul, Ψ.injective.eq_iff]

theorem mem_C_comap (Ψ : Γ ≃* Γ') (F : L3Frame Γ' p k) {x : Γ} :
    x ∈ F.P.comap Ψ.toMonoidHom ⊓ centralizer ({(Ψ.symm F.e) ^ 2} : Set Γ) ↔
      Ψ x ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ') := by
  simp only [mem_inf, mem_comap, MulEquiv.coe_toMonoidHom, mem_centralizer_singleton_iff]
  rw [comm_iff Ψ, map_pow, MulEquiv.apply_symm_apply]

@[expose] noncomputable def comapC (Ψ : Γ ≃* Γ') (F : L3Frame Γ' p k) :
    ↥(F.P.comap Ψ.toMonoidHom ⊓ centralizer ({(Ψ.symm F.e) ^ 2} : Set Γ)) →*
      ↥(F.P ⊓ centralizer ({F.e ^ 2} : Set Γ')) :=
  (Ψ.toMonoidHom.comp (Subgroup.subtype _)).codRestrict _ fun x => (mem_C_comap Ψ F).1 x.2

theorem coe_comapC (Ψ : Γ ≃* Γ') (F : L3Frame Γ' p k)
    (x : ↥(F.P.comap Ψ.toMonoidHom ⊓ centralizer ({(Ψ.symm F.e) ^ 2} : Set Γ))) :
    (comapC Ψ F x : Γ') = Ψ x :=
  rfl

theorem comapC_surjective (Ψ : Γ ≃* Γ') (F : L3Frame Γ' p k) :
    Function.Surjective (comapC Ψ F) := fun y =>
  ⟨⟨Ψ.symm y, (mem_C_comap Ψ F).2 (by rw [MulEquiv.apply_symm_apply]; exact y.2)⟩,
    Subtype.ext (MulEquiv.apply_symm_apply Ψ y)⟩

theorem comapC_injective (Ψ : Γ ≃* Γ') (F : L3Frame Γ' p k) :
    Function.Injective (comapC Ψ F) := fun _ _ h =>
  Subtype.ext (Ψ.injective (congrArg Subtype.val h))

theorem ρ_comapC (Ψ : Γ ≃* Γ') (F : L3Frame Γ' p k) {x : Γ}
    (hx : x ∈ F.P.comap Ψ.toMonoidHom ⊓ centralizer ({(Ψ.symm F.e) ^ 2} : Set Γ)) {y : Γ'}
    (hy : y ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ')) (hxy : Ψ x = y) :
    F.ρ (comapC Ψ F ⟨x, hx⟩) = F.ρ ⟨y, hy⟩ :=
  congrArg F.ρ (Subtype.ext hxy)

theorem comap_centralizer_pair (Ψ : Γ ≃* Γ') (a b : Γ') :
    centralizer ({Ψ.symm a, Ψ.symm b} : Set Γ) =
      (centralizer ({a, b} : Set Γ')).comap Ψ.toMonoidHom := by
  ext x
  simp only [mem_comap, MulEquiv.coe_toMonoidHom, mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  rw [comm_iff Ψ, comm_iff Ψ (g := Ψ.symm b), MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]

theorem isCyclic_comap (Ψ : Γ ≃* Γ') {H : Subgroup Γ'} (hH : IsCyclic ↥H) :
    IsCyclic ↥(H.comap Ψ.toMonoidHom) := by
  let f : ↥(H.comap Ψ.toMonoidHom) →* ↥H :=
    { toFun := fun x => ⟨Ψ (x : Γ), x.2⟩
      map_one' := Subtype.ext (map_one Ψ)
      map_mul' := fun x y => Subtype.ext (map_mul Ψ (x : Γ) (y : Γ)) }
  exact isCyclic_of_injective f fun x y h => Subtype.ext (Ψ.injective (congrArg Subtype.val h))

theorem mem_normalizer_map (Ψ : Γ ≃* Γ') {R : Subgroup Γ} {y : Γ} :
    Ψ y ∈ normalizer ((R.map Ψ.toMonoidHom : Subgroup Γ') : Set Γ') ↔
      y ∈ normalizer (R : Set Γ) := by
  simp only [mem_normalizer_iff, mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · intro h x
    have hx := h (Ψ x)
    constructor
    · intro hxR
      obtain ⟨w, hw, hwe⟩ := hx.1 ⟨x, hxR, rfl⟩
      rw [← map_inv, ← map_mul, ← map_mul] at hwe
      rwa [← Ψ.injective hwe]
    · intro hxR
      obtain ⟨w, hw, hwe⟩ := hx.2 (by
        refine ⟨y * x * y⁻¹, hxR, ?_⟩
        rw [map_mul, map_mul, map_inv])
      rwa [← Ψ.injective hwe]
  · intro h x
    obtain ⟨x', rfl⟩ := Ψ.surjective x
    rw [← map_inv, ← map_mul, ← map_mul]
    constructor
    · rintro ⟨w, hw, hwe⟩
      rw [Ψ.injective hwe] at hw
      exact ⟨_, (h x').1 hw, rfl⟩
    · rintro ⟨w, hw, hwe⟩
      rw [Ψ.injective hwe] at hw
      exact ⟨_, (h x').2 hw, rfl⟩

@[expose] noncomputable def comap (Ψ : Γ ≃* Γ') (F : L3Frame Γ' p k) : L3Frame Γ p k where
  I := F.I.comap Ψ.toMonoidHom
  P := F.P.comap Ψ.toMonoidHom
  e := Ψ.symm F.e
  r := Ψ.symm F.r
  Kb := F.Kb.comap Ψ.toMonoidHom
  Zb := F.Zb.comap Ψ.toMonoidHom
  ρ := F.ρ.comp (comapC Ψ F)
  I_normal := by have := F.I_normal; exact Subgroup.Normal.comap this _
  P_normal := by have := F.P_normal; exact Subgroup.Normal.comap this _
  I_le_P := Subgroup.comap_mono F.I_le_P
  mul_mem_of_not_mem g h hg hh := by
    simp only [mem_comap, MulEquiv.coe_toMonoidHom, map_mul] at hg hh ⊢
    exact F.mul_mem_of_not_mem _ _ hg hh
  mem_I_of_two g hg n hn := by
    simp only [mem_comap, MulEquiv.coe_toMonoidHom] at hg ⊢
    exact F.mem_I_of_two _ hg n (by rw [← map_pow, hn, map_one])
  e_mem := by
    simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact F.e_mem
  r_mem := by
    simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact F.r_mem
  e_pow_four := by rw [← map_pow, F.e_pow_four, map_one]
  r_sq := by rw [← map_pow, F.r_sq, map_one]
  r_e := by rw [← map_inv, ← map_mul, ← map_mul, F.r_e, map_inv]
  e_sq_ne h := F.e_sq_ne (by rw [← map_pow, map_eq_one_iff _ Ψ.symm.injective] at h; exact h)
  isCyclic_cent := by
    rw [comap_centralizer_pair Ψ F.e F.r, ← Subgroup.comap_inf]
    exact isCyclic_comap Ψ F.isCyclic_cent
  isPGroup_D8 := by
    have h : Subgroup.closure ({Ψ.symm F.e, Ψ.symm F.r} : Set Γ) =
        (Subgroup.closure ({F.e, F.r} : Set Γ')).map Ψ.symm.toMonoidHom := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [h]
    exact F.isPGroup_D8.map _
  Kb_le x hx := by
    rw [mem_C_comap Ψ F]
    exact F.Kb_le hx
  conj_mem_Kb g hg x hx := by
    simp only [mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv] at hx ⊢
    refine F.conj_mem_Kb _ ?_ _ hx
    rw [comm_iff Ψ, map_pow, MulEquiv.apply_symm_apply] at hg
    exact hg
  mem_Zb x := by
    simp only [mem_comap, MulEquiv.coe_toMonoidHom]
    rw [F.mem_Zb, mem_C_comap Ψ F]
    refine and_congr_right fun _ => ⟨fun h y hy => ?_, fun h y hy => ?_⟩
    · rw [comm_iff Ψ]
      exact h _ ((mem_C_comap Ψ F).1 hy)
    · have h' := h (Ψ.symm y) ((mem_C_comap Ψ F).2 (by rw [MulEquiv.apply_symm_apply]; exact hy))
      rwa [comm_iff Ψ, MulEquiv.apply_symm_apply] at h'
  isCyclic_Zb := isCyclic_comap Ψ F.isCyclic_Zb
  eq_one_of_mem_Kb_Zb x hxK hxZ hx := by
    simp only [mem_comap, MulEquiv.coe_toMonoidHom] at hxK hxZ
    have h := F.eq_one_of_mem_Kb_Zb _ hxK hxZ (by rwa [MulEquiv.orderOf_eq])
    exact (map_eq_one_iff _ Ψ.injective).1 h
  ρ_eq_one x := by
    rw [MonoidHom.comp_apply, F.ρ_eq_one, coe_comapC]
    rfl
  eight_dvd := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ (comapC_surjective Ψ F),
      ← MonoidHom.range_eq_map]
    exact F.eight_dvd
  ρ_ne he hr := by
    have he' := (mem_C_comap Ψ F).1 he
    have hr' := (mem_C_comap Ψ F).1 hr
    rw [MulEquiv.apply_symm_apply] at he' hr'
    simp only [MonoidHom.comp_apply]
    rw [ρ_comapC Ψ F he he' (MulEquiv.apply_symm_apply Ψ F.e),
      ρ_comapC Ψ F hr hr' (MulEquiv.apply_symm_apply Ψ F.r)]
    exact F.ρ_ne he' hr'
  isPGroup_of_comm he hr g h1 h2 := by
    have he' := (mem_C_comap Ψ F).1 he
    have hr' := (mem_C_comap Ψ F).1 hr
    rw [MulEquiv.apply_symm_apply] at he' hr'
    simp only [MonoidHom.comp_apply] at h1 h2
    rw [ρ_comapC Ψ F he he' (MulEquiv.apply_symm_apply Ψ F.e)] at h1
    rw [ρ_comapC Ψ F hr hr' (MulEquiv.apply_symm_apply Ψ F.r)] at h2
    exact F.isPGroup_of_comm he' hr' g h1 h2
  not_unip u h3 hρ h1 h2 := by
    refine F.not_unip (comapC Ψ F u) (by rwa [coe_comapC, MulEquiv.orderOf_eq]) hρ ?_ ?_
    · rw [coe_comapC]
      have h := (comm_iff Ψ).1 h1
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h
    · rw [coe_comapC]
      have h := (comm_iff Ψ).1 h2
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h
  mem_Kb_of_inv x w hx hw := by
    simp only [mem_comap, MulEquiv.coe_toMonoidHom]
    refine F.mem_Kb_of_inv (comapC Ψ F x) (comapC Ψ F w)
      (by rwa [orderOf_injective _ (comapC_injective Ψ F)]) ?_
    rw [← map_inv, ← map_mul, ← map_mul, hw, map_inv]
  comm_of_comm_Kb x hx hx1 hxc g hg hgx := by
    simp only [mem_comap, MulEquiv.coe_toMonoidHom] at hx hg
    rw [comm_iff Ψ, map_pow, MulEquiv.apply_symm_apply]
    exact F.comm_of_comm_Kb _ hx ((map_ne_one_iff _ Ψ.injective).2 hx1)
      (by rwa [MulEquiv.orderOf_eq]) _ hg ((comm_iff Ψ).1 hgx)
  comm_of_comm_Zb d hd hd1 hdo g hg hgd := by
    simp only [mem_comap, MulEquiv.coe_toMonoidHom] at hd hg
    rw [comm_iff Ψ, map_pow, MulEquiv.apply_symm_apply]
    exact F.comm_of_comm_Zb _ hd ((map_ne_one_iff _ Ψ.injective).2 hd1)
      (by rwa [MulEquiv.orderOf_eq]) _ hg ((comm_iff Ψ).1 hgd)
  not_inv_Zb d hd hd1 hdo g hg h := by
    simp only [mem_comap, MulEquiv.coe_toMonoidHom] at hd hg
    refine F.not_inv_Zb _ hd ((map_ne_one_iff _ Ψ.injective).2 hd1)
      (by rwa [MulEquiv.orderOf_eq]) _ hg ?_
    rw [← map_inv, ← map_mul, ← map_mul, h, map_inv]
  comm_of_abelian A B hAB hBP hBab h3 h5 h6 he hr a ha := by
    have hinj : Function.Injective Ψ.toMonoidHom := Ψ.injective
    have hB : IsMulCommutative ↥(B.map Ψ.toMonoidHom) := by
      refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
      obtain ⟨x', hx', hxe⟩ := x.2
      obtain ⟨y', hy', hye⟩ := y.2
      have h := congrArg Subtype.val (hBab.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩)
      simp only [Subgroup.coe_mul] at h ⊢
      rw [← hxe, ← hye, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, h]
    have h := F.comm_of_abelian (A.map Ψ.toMonoidHom) (B.map Ψ.toMonoidHom) (map_mono hAB)
      (by rw [map_le_iff_le_comap]; exact hBP) hB
      (by rwa [card_map_of_injective hinj]) (by rwa [card_map_of_injective hinj])
      (by rwa [card_map_of_injective hinj])
      (by rw [← MulEquiv.apply_symm_apply Ψ F.e]; exact (mem_normalizer_map Ψ).2 he)
      (by rw [← MulEquiv.apply_symm_apply Ψ F.r]; exact (mem_normalizer_map Ψ).2 hr)
      (Ψ a) ⟨a, ha, rfl⟩
    rw [comm_iff Ψ, map_pow, MulEquiv.apply_symm_apply]
    exact h
  exists_conj_Kb v hv := by
    rw [comm_iff Ψ, map_pow, MulEquiv.apply_symm_apply] at hv
    obtain ⟨g, hg, hgK⟩ := F.exists_conj_Kb (Ψ v) hv
    refine ⟨Ψ.symm g, (mem_C_comap Ψ F).2 (by rw [MulEquiv.apply_symm_apply]; exact hg),
      fun x hx => Ψ.injective ?_⟩
    simp only [mem_comap, MulEquiv.coe_toMonoidHom] at hx
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hgK _ hx
  comm_of_coprime_six y hy hy6 R hR hyR x hx := by
    simp only [mem_comap, MulEquiv.coe_toMonoidHom] at hy
    rw [comm_iff Ψ]
    exact F.comm_of_coprime_six _ hy (by rwa [MulEquiv.orderOf_eq]) (R.map Ψ.toMonoidHom)
      (hR.map _) ((mem_normalizer_map Ψ).2 hyR) (Ψ x) ⟨x, hx, rfl⟩

theorem comap_I (Ψ : Γ ≃* Γ') (F : L3Frame Γ' p k) : (comap Ψ F).I = F.I.comap Ψ.toMonoidHom :=
  rfl

theorem comap_Kb (Ψ : Γ ≃* Γ') (F : L3Frame Γ' p k) :
    (comap Ψ F).Kb = F.Kb.comap Ψ.toMonoidHom :=
  rfl

end L3Frame

end CFSG.LocalAnalysis.UniquenessCase.UC22
