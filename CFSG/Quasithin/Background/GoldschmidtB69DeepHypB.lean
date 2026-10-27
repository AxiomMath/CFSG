module

public import CFSG.Quasithin.Background.GoldschmidtB69DeepHypA

public section

namespace CFSG.Quasithin.B69.Hyp

open CFSG.Quasithin.HatA6 CFSG.CharacterTheory.SteinbergBY

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_hyperoval (hsq2 : ∀ v : V, v ^ 2 = 1) (hV : Nat.card V = 2 ^ 6)
    {L : Subgroup (MulAut V)} (hperf : Group.IsPerfect ↥L)
    (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6))
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤) :
    ∃ ρ : ↥L →* Equiv.Perm (Fin 6), ρ.range = alternatingGroup (Fin 6) ∧
      ∀ x : MulAut V, (∀ l, l ∈ L ↔ x * l * x⁻¹ ∈ L) →
        ∃ g : Equiv.Perm (Fin 6), ∀ l l' : ↥L, (l' : MulAut V) = x * l * x⁻¹ →
          ρ l' = g * ρ l * g⁻¹ := by
  classical
  obtain ⟨zL, hcen, h3, hfp⟩ := exists_center_fpf hsq2 hV hperf hZ e
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hsq2 v
  set z : MulAut V := (zL : MulAut V) with hzdef
  have hzz : ∀ w, z (z w) = w * z w := fun w =>
    H13.zz_eq_of_fpf hsq2 h3 (W := ⊤) (fun _ _ => trivial) (fun w _ hw => hfp w hw) trivial
  obtain ⟨u, hb⟩ := exists_coord hsq hV h3 hfp
  have hzc : zL ∈ Subgroup.center ↥L := hcen ▸ Subgroup.mem_zpowers zL
  have hLz : ∀ l ∈ L, ∀ w, l (z w) = z (l w) := by
    intro l hl w
    have h1 := Subgroup.mem_center_iff.1 hzc ⟨l, hl⟩
    exact congrArg (fun y : ↥L => (y : MulAut V) w) h1
  have hperf' : commutator ↥L = ⊤ := Group.isPerfect_def.1 hperf
  have hfpf : ∀ k ∈ Subgroup.center ↥L, k ≠ 1 → ∀ v : V, (k : MulAut V) v = v → v = 1 := by
    intro k hk hk1 v hv
    rw [hcen] at hk
    obtain ⟨n, hn0⟩ := (mem_powers_iff_mem_zpowers).2 hk
    have hn0' : zL ^ n = k := hn0
    rw [← hn0'] at hk1 hv
    have hz3 : zL ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h3)
    have hn : zL ^ n = zL ^ (n % 3) := by
      conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hz3, one_pow, one_mul]
    rw [hn] at hk1 hv
    have hn3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases (n % 3)
    · exact absurd (pow_zero zL) hk1
    · exact hfp v (by simpa using hv)
    · apply hfp v
      have h2 : z (z v) = v := by simpa [pow_two, MulAut.mul_apply] using hv
      calc z v = z (z (z v)) := by rw [h2]
        _ = v := by
          have := congrArg (fun y : MulAut V => y v) h3
          simpa [pow_succ, MulAut.mul_apply] using this
  obtain ⟨f, hf1, hf⟩ := H13.Orbit.hatA6_orbits hV hperf' hZ e hfpf
  set O := H13.Orbit.orbitIn L f with hOdef
  have hO : ∀ l ∈ L, ∀ v ∈ O, l v ∈ O := by
    rintro l hl _ ⟨m, hm, rfl⟩
    exact ⟨l * m, L.mul_mem hl hm, rfl⟩
  have hfO : f ∈ O := ⟨1, L.one_mem, rfl⟩
  have hOcard : Nat.card O = 18 := (hf f hf1).1 hfO
  have h1O : (1 : V) ∉ O := by
    rintro ⟨m, -, hm⟩
    apply hf1
    have := congrArg (fun w => m⁻¹ w) hm
    simpa using this
  have hcardP : Fintype.card ↥(pts hb O) = 6 := by
    rw [Fintype.card_coe]
    exact card_pts_eq hb hzz hO rfl hOcard h1O
  have hrange := range_ptPerm hb hzz hLz hO hirr hV rfl hcen e hOcard h1O
  let eP : ↥(pts hb O) ≃ Fin 6 := Fintype.equivFinOfCardEq hcardP
  let ρ : ↥L →* Equiv.Perm (Fin 6) :=
    eP.permCongrHom.toMonoidHom.comp (ptPerm hb hzz hLz O hO)
  refine ⟨ρ, ?_, ?_⟩
  · ext σ
    rw [Equiv.Perm.mem_alternatingGroup]
    constructor
    · rintro ⟨l, rfl⟩
      have hl : ptPerm hb hzz hLz O hO l ∈ alternatingGroup ↥(pts hb O) :=
        hrange ▸ ⟨l, rfl⟩
      rw [Equiv.Perm.mem_alternatingGroup] at hl
      show Equiv.Perm.sign (eP.permCongr (ptPerm hb hzz hLz O hO l)) = 1
      rw [Equiv.Perm.sign_permCongr, hl]
    · intro hσ
      have hσ' : eP.permCongrHom.symm σ ∈ (ptPerm hb hzz hLz O hO).range := by
        rw [hrange, Equiv.Perm.mem_alternatingGroup]
        show Equiv.Perm.sign (eP.permCongrHom.symm σ) = 1
        rw [Equiv.permCongrHom_symm]
        show Equiv.Perm.sign (eP.symm.permCongr σ) = 1
        rw [Equiv.Perm.sign_permCongr, hσ]
      obtain ⟨l, hl⟩ := hσ'
      refine ⟨l, ?_⟩
      show eP.permCongrHom (ptPerm hb hzz hLz O hO l) = σ
      rw [hl, MulEquiv.apply_symm_apply]
  · intro x hxN
    have hxO : ∀ v ∈ O, x v ∈ O := by
      intro v hv
      have hv1 : v ≠ 1 := fun h => h1O (h ▸ hv)
      have hxv1 : x v ≠ 1 := fun h => hv1 (x.injective (h.trans (map_one x).symm))
      have hvO : H13.Orbit.orbitIn L v = O := by
        obtain ⟨m, hm, rfl⟩ := hv
        ext w
        constructor
        · rintro ⟨n, hn, rfl⟩
          exact ⟨n * m, L.mul_mem hn hm, rfl⟩
        · rintro ⟨n, hn, rfl⟩
          refine ⟨n * m⁻¹, L.mul_mem hn (L.inv_mem hm), ?_⟩
          simp [MulAut.mul_apply]
      by_contra hcon
      have h18 : Nat.card (H13.Orbit.orbitIn L (x v)) = 18 := by
        rw [card_orbitIn_map hxN v, hvO, hOcard]
      have h45 := (hf (x v) hxv1).2 hcon
      omega
    have hxinv : ∀ l ∈ L, x⁻¹ * l * x ∈ L := fun l hl => by
      rw [hxN]
      have : x * (x⁻¹ * l * x) * x⁻¹ = l := by group
      rw [this]
      exact hl
    obtain ⟨n, hn⟩ : ∃ n : ℕ, x * z * x⁻¹ = z ^ n := by
      have hm : x * z * x⁻¹ ∈ L := (hxN z).1 zL.2
      have hmc : (⟨x * z * x⁻¹, hm⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro l₀
        have hcomm := Subgroup.mem_center_iff.1 hzc ⟨x⁻¹ * l₀ * x, hxinv l₀ l₀.2⟩
        have hcomm' : (x⁻¹ * (l₀ : MulAut V) * x) * z = z * (x⁻¹ * (l₀ : MulAut V) * x) :=
          congrArg Subtype.val hcomm
        apply Subtype.ext
        show (l₀ : MulAut V) * (x * z * x⁻¹) = (x * z * x⁻¹) * (l₀ : MulAut V)
        calc (l₀ : MulAut V) * (x * z * x⁻¹)
            = x * ((x⁻¹ * (l₀ : MulAut V) * x) * z) * x⁻¹ := by group
          _ = x * (z * (x⁻¹ * (l₀ : MulAut V) * x)) * x⁻¹ := by rw [hcomm']
          _ = (x * z * x⁻¹) * (l₀ : MulAut V) := by group
      rw [hcen] at hmc
      obtain ⟨n, hn0⟩ := (mem_powers_iff_mem_zpowers).2 hmc
      refine ⟨n, ?_⟩
      have := congrArg Subtype.val (show zL ^ n = ⟨x * z * x⁻¹, hm⟩ from hn0)
      rw [Subgroup.coe_pow] at this
      exact this.symm
    have hxz : ∀ w, x (z w) = (z ^ n) (x w) := by
      intro w
      have := congrArg (fun y : MulAut V => y (x w)) hn
      simpa [MulAut.mul_apply] using this
    have hex : ∀ p : ↥(pts hb O), ∃ p' : ↥(pts hb O),
        subOf hb (p' : Submodule FieldFour (Fin 3 → FieldFour)) =
          (subOf hb (p : Submodule FieldFour (Fin 3 → FieldFour))).map x.toMonoidHom := by
      intro p
      obtain ⟨c, hc, hcp⟩ := (mem_pts hb O).1 p.2
      have hvO : coordEquiv hb (Multiplicative.ofAdd c) ∈ O := (mem_okSet hb O).1 hc
      have hxvO := hxO _ hvO
      have hv' : coordEquiv hb (Multiplicative.ofAdd (Multiplicative.toAdd
          ((coordEquiv hb).symm (x (coordEquiv hb (Multiplicative.ofAdd c)))))) =
            x (coordEquiv hb (Multiplicative.ofAdd c)) := by
        rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
      refine ⟨⟨FieldFour ∙ Multiplicative.toAdd
        ((coordEquiv hb).symm (x (coordEquiv hb (Multiplicative.ofAdd c)))),
        (mem_pts hb O).2 ⟨_, (mem_okSet hb O).2 (by rw [hv']; exact hxvO), rfl⟩⟩, ?_⟩
      rw [← hcp]
      exact (map_subOf_eq hb hzz hxz h1O hvO hxvO).symm
    choose σf hσf using hex
    have hinj : Function.Injective σf := by
      intro p q hpq
      have h1 := hσf p
      have h2 := hσf q
      rw [hpq] at h1
      have h3 := Subgroup.map_injective (f := x.toMonoidHom) x.injective (h1.symm.trans h2)
      exact Subtype.ext (subOf_injective hb h3)
    let σ : Equiv.Perm ↥(pts hb O) := Equiv.ofBijective σf (Finite.injective_iff_bijective.1 hinj)
    refine ⟨eP.permCongr σ, fun l l' hl' => ?_⟩
    have hkey : ∀ q : ↥(pts hb O),
        ptPerm hb hzz hLz O hO l' (σ q) = σ (ptPerm hb hzz hLz O hO l q) := by
      intro q
      apply Subtype.ext
      apply subOf_injective hb
      show subOf hb ((σf q : Submodule FieldFour (Fin 3 → FieldFour)).map (linL hb hzz hLz l')) = _
      rw [subOf_map_linL hb hzz hLz, hσf q]
      show _ = subOf hb (σf (ptPerm hb hzz hLz O hO l q) : Submodule FieldFour (Fin 3 → FieldFour))
      rw [hσf (ptPerm hb hzz hLz O hO l q), ptPerm_apply, ptAct_coe, subOf_map_linL hb hzz hLz,
        Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext w
      have := congrArg (fun y : MulAut V => y (x w)) hl'
      simpa [MulAut.mul_apply] using this
    have hperm : ptPerm hb hzz hLz O hO l' = σ * ptPerm hb hzz hLz O hO l * σ⁻¹ := by
      refine Equiv.ext fun p => ?_
      have h := hkey (σ.symm p)
      rw [Equiv.apply_symm_apply] at h
      rw [h]
      rfl
    show eP.permCongrHom (ptPerm hb hzz hLz O hO l') =
      eP.permCongrHom σ * eP.permCongrHom (ptPerm hb hzz hLz O hO l) * (eP.permCongrHom σ)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, hperm]

end CFSG.Quasithin.B69.Hyp
