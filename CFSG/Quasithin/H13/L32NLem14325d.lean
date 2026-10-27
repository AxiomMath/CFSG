module

public import CFSG.Quasithin.H13.L32NLem14325c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14325

theorem genFittingLayer_le_commutator (X : Type*) [Group X] :
    genFittingLayer X ≤ commutator X := by
  refine sSup_le fun L hL => ?_
  obtain ⟨-, -, hq, -⟩ := hL
  have h1 : (commutator ↥L).map L.subtype = L := by
    rw [hq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← h1, commutator_def, Subgroup.map_commutator]
  exact Subgroup.commutator_mono le_top le_top

theorem s5_exists_conj_five : ∀ σ : Equiv.Perm (Fin 5), σ * σ = 1 → σ ≠ 1 →
    Equiv.Perm.sign σ = 1 →
    ∃ τ ∈ [Equiv.swap 1 2 * Equiv.swap 3 4, Equiv.swap 0 2 * Equiv.swap 3 4,
      Equiv.swap 1 3 * Equiv.swap 2 4, Equiv.swap 0 1 * Equiv.swap 2 4,
      Equiv.swap 0 3 * Equiv.swap 1 4, Equiv.swap 1 2 * Equiv.swap 0 4],
      (σ * (τ * σ * τ⁻¹)) ^ 5 = 1 ∧ σ * (τ * σ * τ⁻¹) ≠ 1 := by
  decide +kernel

variable {G : Type} [Group G]

theorem map_conj_centralizer (h x : G) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj h).toMonoidHom =
      Subgroup.centralizer ({h * x * h⁻¹} : Set G) := by
  ext z
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    calc h * w * h⁻¹ * (h * x * h⁻¹) = h * (w * x) * h⁻¹ := by group
      _ = h * (x * w) * h⁻¹ := by rw [hw]
      _ = h * x * h⁻¹ * (h * w * h⁻¹) := by group
  · intro hz
    refine ⟨h⁻¹ * z * h, ?_, by group⟩
    calc h⁻¹ * z * h * x = h⁻¹ * (z * (h * x * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x * h⁻¹) * z) * h := by rw [hz]
      _ = x * (h⁻¹ * z * h) := by group

variable [Finite G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

namespace Ctx14325

variable (C : Ctx14325 G T L V V₂ g D)
include C

omit [Finite G] C in
theorem card_V_of_dim (hd : Module.finrank (ZMod 2) D.V = 4) : Nat.card D.V = 16 := by
  have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd, Nat.card_zmod]
  norm_num

theorem false_of_five (hd : Module.finrank (ZMod 2) D.V = 4) {y : G} (hyH : y ∈ l32nH T V)
    {k : ℕ} (hy : y ^ (5 ^ k) = 1) (hyc : y ∈ Subgroup.centralizer (vH T L V : Set G))
    (hy1 : D.ρ ⟨y, L14332.l32nH_le_normalizer_fsuU T V hyH⟩ ≠ 1) : False := by
  set γ := D.ρ ⟨y, L14332.l32nH_le_normalizer_fsuU T V hyH⟩ with hγ
  have hγk : γ ^ (5 ^ k) = 1 := by
    rw [hγ, ← map_pow]
    have : (⟨y, L14332.l32nH_le_normalizer_fsuU T V hyH⟩ :
        ↥(Subgroup.normalizer (fsuU T V : Set G))) ^ (5 ^ k) = 1 := Subtype.ext (by simpa using hy)
    rw [this, map_one]
  have hfix := fix_of_maps_card_four C.card_hatV (p := 5) (by norm_num) le_rfl hγk
    (fun s hs => C.rho_mem_hatV hyH hyc hs)
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ D.hat V, w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hb : D.hat V = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
    have := C.card_hatV
    rw [hb] at this
    simp at this
  exact hy1 (eq_one_of_fix_card_sixteen (card_V_of_dim hd) hγk hw0 (hfix w hw))

theorem not_case_ii (h12810 : Lemma12_8_10) (hd : Module.finrank (ZMod 2) D.V = 4)
    (hii : Case14323ii T V g D) : False := by
  have := L14332.finite_linearEquiv D
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := hii.iso
  set Hd := D.img (l32nH T V) with hHd
  set Zd := D.img (CFSG.conjugate (centerOf (fsuU T V)) g) with hZd
  set Ψ : ↥(l32nH T V) →* Equiv.Perm (Fin 5) :=
    (e : ↥Hd →* Equiv.Perm (Fin 5)).comp (L14332.imgHom D) with hΨ
  have hΨs : Function.Surjective Ψ := e.surjective.comp (L14332.imgHom_surjective D)
  obtain ⟨⟨γ, hγZ⟩, hγ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp C.zUg_ne
  obtain ⟨x, hx, hxN, hxγ⟩ := (L128A.HatU.mem_img D).mp hγZ
  have hxH : x ∈ l32nH T V := C.zUg_le hx
  set xH : ↥(l32nH T V) := ⟨x, hxH⟩ with hxHdef
  have himgx : ((L14332.imgHom D xH : ↥Hd) : D.V ≃ₗ[ZMod 2] D.V) = γ := by
    rw [L14332.imgHom_apply, ← hxγ]
  have hγ1' : γ ≠ 1 := fun h => hγ1 (Subtype.ext h)
  set σ := Ψ xH with hσ
  have hγ2 : γ * γ = 1 := by
    have h2 := pow_card_eq_one' (G := ↥Zd) (x := ⟨γ, hγZ⟩)
    rw [hii.card_zU, pow_two] at h2
    exact congrArg Subtype.val h2
  have himg2 : L14332.imgHom D xH * L14332.imgHom D xH = 1 :=
    Subtype.ext (by rw [Subgroup.coe_mul, himgx, hγ2]; rfl)
  have hσ2 : σ * σ = 1 := by
    rw [hσ, hΨ, MonoidHom.comp_apply, ← map_mul, himg2, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    have h1' : e (L14332.imgHom D xH) = 1 := h1
    rw [MulEquiv.map_eq_one_iff] at h1'
    exact hγ1' (by rw [← himgx, h1']; rfl)
  have hσA : Equiv.Perm.sign σ = 1 := by
    obtain ⟨z, hz, hzγ⟩ := hii.zU_le hγZ
    have hz' : z = L14332.imgHom D xH := Subtype.ext (by rw [himgx]; exact hzγ)
    have hzc := genFittingLayer_le_commutator ↥Hd hz
    have hzc' : e z ∈ commutator (Equiv.Perm (Fin 5)) := by
      have hm := Subgroup.mem_map_of_mem (e : ↥Hd →* Equiv.Perm (Fin 5)) hzc
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective] at hm
      exact hm
    have := alternatingGroup.commutator_perm_le hzc'
    rw [Equiv.Perm.mem_alternatingGroup] at this
    rw [hσ, hΨ, MonoidHom.comp_apply, ← hz']
    exact this
  obtain ⟨τ, -, hτ5, hτ1⟩ := s5_exists_conj_five σ hσ2 hσ1 hσA
  obtain ⟨hH, hhH⟩ := hΨs τ
  set u : ↥(l32nH T V) := xH * (hH * xH * hH⁻¹) with hu
  have hΨu : Ψ u = σ * (τ * σ * τ⁻¹) := by
    rw [hu, map_mul, map_mul, map_mul, map_inv, hhH]
  have hou : orderOf (Ψ u) = 5 := by
    rw [hΨu]
    exact orderOf_eq_prime hτ5 hτ1
  have ho0 : orderOf u ≠ 0 := (orderOf_pos u).ne'
  obtain ⟨k, m, hm5, hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho0 5 (by norm_num)
  set y : ↥(l32nH T V) := u ^ m with hy
  have hyk : (y : G) ^ (5 ^ k) = 1 := by
    have : y ^ (5 ^ k) = 1 := by
      rw [hy, ← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
    simpa using congrArg Subtype.val this
  have hΨy : Ψ y ≠ 1 := by
    intro h1
    rw [hy, map_pow] at h1
    exact hm5 (hou ▸ orderOf_dvd_of_pow_eq_one h1)
  have hρy : D.ρ ⟨y, L14332.l32nH_le_normalizer_fsuU T V y.2⟩ ≠ 1 := by
    intro h1
    apply hΨy
    have : L14332.imgHom D y = 1 := Subtype.ext (by rw [L14332.imgHom_apply]; exact h1)
    rw [hΨ, MonoidHom.comp_apply, this, map_one]
  set x' : G := hH * x * (hH : G)⁻¹ with hx'
  have hvHn : ∀ a ∈ l32nH T V, ∀ w ∈ vH T L V, a * w * a⁻¹ ∈ vH T L V := fun a ha w hw =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ ha) w).mp hw
  have hidx1 := C.relIndex_centralizer_le h12810 hx
  rw [hii.card_zU] at hidx1
  have hidx2 : (vH T L V ⊓ Subgroup.centralizer ({x'} : Set G)).relIndex (vH T L V) ≤ 2 := by
    have hmapV : (vH T L V).map (MulAut.conj (hH : G)).toMonoidHom = vH T L V := by
      have := conjugate_eq_of_mem_normalizer
        (le_normalizer_conjClosure (zL T L V) (l32nH T V) ((l32nH T V).inv_mem hH.2))
      unfold CFSG.conjugate at this
      rwa [inv_inv] at this
    have hmap : (vH T L V ⊓ Subgroup.centralizer ({x} : Set G)).map
        (MulAut.conj (hH : G)).toMonoidHom = vH T L V ⊓ Subgroup.centralizer ({x'} : Set G) := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj (hH : G)).injective, hmapV,
        map_conj_centralizer]
    rw [← hmap, ← hmapV, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj _).injective,
      hmapV]
    exact hidx1
  have hidx : (vH T L V ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      (vH T L V ⊓ Subgroup.centralizer ({x'} : Set G))).relIndex (vH T L V) ≤ 4 :=
    Subgroup.relIndex_inf_le.trans (by
      calc _ ≤ 2 * 2 := Nat.mul_le_mul hidx1 hidx2
        _ = 4 := by norm_num)
  have hred := C.red.2.2.1
  have hyc : ∀ w ∈ vH T L V, (y : G) * w * (y : G)⁻¹ = w := by
    refine centralizes_of_pow_five (W := vH T L V) (fun w hw => by
      have := hred.2 w hw
      rwa [pow_two] at this) (fun v hv w hw => congrArg Subtype.val
        (hred.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)) hidx (k := k) (hvHn _ y.2) (fun w _ => by
          rw [hyk]; group) ?_
    rintro c ⟨⟨-, hcx⟩, -, hcx'⟩
    have hcx1 := Subgroup.mem_centralizer_singleton_iff.mp hcx
    have hcx2 := Subgroup.mem_centralizer_singleton_iff.mp hcx'
    have hcu : (u : G) * c = c * u := by
      change x * x' * c = c * (x * x')
      rw [mul_assoc, ← hcx2, ← mul_assoc, ← hcx1, mul_assoc]
    have hcy : (y : G) * c = c * y := by
      rw [hy, Subgroup.coe_pow]
      exact (Commute.pow_left hcu m).eq
    rw [hcy]
    group
  refine C.false_of_five hd y.2 hyk ?_ hρy
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  calc w * y = (y * w * (y : G)⁻¹) * y := by rw [hyc w hw]
    _ = y * w := by group

end Ctx14325

end L14325

end CFSG.Quasithin.H13
