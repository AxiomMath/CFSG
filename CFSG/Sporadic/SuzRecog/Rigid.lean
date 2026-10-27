module

public import CFSG.Sporadic.SuzRecog.SettingType
public import CFSG.Sporadic.SuzRecog.Fibre
public import CFSG.Sporadic.SuzRecog.TwistCount
public import CFSG.Sporadic.SuzRecog.SwapCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.ComponentClassification.AS81
  CFSG.ComponentClassification.AS81.SuzB0 CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Co1Patterson

section Twist

variable
  {E : Type} [Group E] {π : E →* Lm} {ζ : E} (hζ : π ζ = 1)

@[expose] noncomputable def twTau : Twist nativeType π ζ hζ →* Lm :=
  QuotientGroup.lift (normalClosure {zζ nativeType π ζ hζ})
    ((nativeType.φ.comp (MonoidHom.fst _ E)).comp (fibreProd nativeType.φ π).subtype) (by
      refine normalClosure_le_normal ?_
      rintro _ rfl
      exact nativeType.φ_z)

theorem isPGroup_ker_twTau (hker : ∀ e, π e = 1 ↔ e = 1 ∨ e = ζ) (hζ2 : ζ * ζ = 1) :
    IsPGroup 2 (twTau hζ).ker := by
  rintro ⟨x, hx⟩
  obtain ⟨⟨⟨h, e⟩, hf⟩, rfl⟩ := QuotientGroup.mk_surjective x
  have hh : nativeType.φ h = 1 := hx
  have he : π e = 1 := by rw [← mem_fibreProd.1 hf]; exact hh
  have hh4 : h * h * (h * h) = 1 := by
    rcases (CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one
      (qMinus (nativeType.vec h))) with h0 | h1
    · rw [(nativeType.mul_self_eq_one_iff h hh).2 h0, one_mul]
    · rw [(nativeType.mul_self_eq_z_iff h hh).2 h1, nativeType.z_mul_self]
  have he2 : e * e = 1 := by
    rcases (hker e).1 he with rfl | rfl
    · exact one_mul 1
    · exact hζ2
  refine ⟨2, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, OneMemClass.coe_one, ← QuotientGroup.mk_pow]
  refine (QuotientGroup.eq_one_iff _).2 ?_
  have : (⟨(h, e), hf⟩ : fibreProd nativeType.φ π) ^ 2 ^ 2 = 1 := by
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    ext
    · simp only [Prod.pow_fst, Prod.fst_one]
      rw [show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add, pow_two, hh4]
    · simp only [Prod.pow_snd, Prod.snd_one]
      rw [show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add, pow_two, he2, one_mul]
  rw [this]
  exact one_mem _

end Twist

variable {G : Type} [Group G] [Finite G] (S : CFSG.LargeExtraspecial.Setting G)

omit [Finite G] in
theorem eq_one_or_eq_zM_of_mem_center {c : S.M} (hc : c ∈ center S.M) : c = 1 ∨ c = S.zM := by
  have hcQ : c ∈ S.Q := S.centralizer_le (mem_centralizer_iff.mpr fun q _ =>
    mem_center_iff.mp hc q)
  have hcZ : (⟨c, hcQ⟩ : S.Q) ∈ center S.Q :=
    mem_center_iff.mpr fun q => Subtype.ext (mem_center_iff.mp hc q)
  rcases S.mem_center_Q_iff.mp hcZ with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

omit [Finite G] in
theorem map_zM_eq {T : Type*} [Group T] (σ : S.M ≃* T) {zT : T} (hzT : zT ∈ center T)
    (hzT1 : zT ≠ 1) : σ S.zM = zT := by
  have hc : σ.symm zT ∈ center S.M := by
    rw [mem_center_iff]
    intro g
    apply σ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact mem_center_iff.mp hzT (σ g)
  rcases eq_one_or_eq_zM_of_mem_center S hc with h | h
  · exact absurd (by rw [← σ.apply_symm_apply zT, h, map_one]) hzT1
  · rw [← h, MulEquiv.apply_symm_apply]

theorem false_of_twist
    (hw : S.width = 3)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hNWC : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) {E : Type} [Group E] [Finite E]
    (hE : commutator E = ⊤) (π : E →* Lm) (hπ : Function.Surjective π) {ζ : E}
    (hζc : ζ ∈ center E) (hker : ∀ e, π e = 1 ↔ e = 1 ∨ e = ζ) (hζ1 : ζ ≠ 1) (hζ : π ζ = 1)
    (σ : S.M ≃* Twist nativeType π ζ hζ) : False := by
  have hζc' : ∀ e, ζ * e = e * ζ := fun e => (mem_center_iff.mp hζc e).symm
  have hζ2 : ζ * ζ = 1 := by
    rcases (hker (ζ * ζ)).1 (by rw [map_mul, hζ, mul_one]) with h | h
    · exact h
    · exact absurd (by simpa using h) hζ1
  have hw₀ : nativeType.φ w0C = 1 := (phi0_eq_one_iff w0C).2 w0P_mem
  obtain ⟨w', hw'⟩ : ∃ x, x = twW nativeType hζ hw₀ := ⟨_, rfl⟩
  obtain ⟨zT, hzT⟩ : ∃ x, x = twZ nativeType hζ := ⟨_, rfl⟩
  have hw0sq : w0C * w0C = 1 := Subtype.ext (by
    have h := coord_qVec.mul_self_eq (v := 1) (by norm_num) 0
    simp only [pow_zero, mul_one, show qMinusBit 1 = 0 by decide] at h
    exact h)
  have hw01 : w0C ≠ 1 := fun h => by
    have := coord_qVec.inj 1 (by norm_num) 0 (by norm_num) 0 (by norm_num) 0 (by norm_num) (by
      simp only [pow_zero, mul_one, coord_qVec.q_zero]
      exact congrArg Subtype.val h)
    omega
  have hw0t : w0C ≠ t1C := fun h => by
    have := coord_qVec.inj 1 (by norm_num) 0 (by norm_num) 0 (by norm_num) 1 (by norm_num) (by
      simp only [pow_zero, mul_one, pow_one, coord_qVec.q_zero, one_mul]
      exact congrArg Subtype.val h)
    omega
  have hw'1 : w' ≠ 1 := by
    intro h
    rw [hw', twW, twMk, ← QuotientGroup.mk_one, mk_eq_mk_iff_twist nativeType hζ hζc' hζ2] at h
    rcases h with h | h
    · exact hw01 (congrArg (fun x : fibreProd nativeType.φ π => x.1.1) h).symm
    · exact hζ1 (by
        have := congrArg (fun x : fibreProd nativeType.φ π => x.1.2) h
        simpa [zζ] using this.symm)
  have hw'2 : w' * w' = 1 := by
    rw [hw', twW, twMk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_one]
    congr 1
    apply Subtype.ext
    simp [hw0sq]
  have hzT1 : zT ≠ 1 := by
    intro h
    rw [hzT, twZ, twMk, ← QuotientGroup.mk_one, mk_eq_mk_iff_twist nativeType hζ hζc' hζ2] at h
    rcases h with h | h
    · exact nativeType.z_ne_one (congrArg (fun x : fibreProd nativeType.φ π => x.1.1)
        h).symm
    · exact hζ1 (by
        have := congrArg (fun x : fibreProd nativeType.φ π => x.1.2) h
        simpa [zζ] using this.symm)
  have hzTc : zT ∈ center (Twist nativeType π ζ hζ) := by
    rw [mem_center_iff]
    intro x
    obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hzT, twZ, twMk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · show f.1.1 * nativeType.z = nativeType.z * f.1.1
      exact nativeType.z_comm f.1.1
    · simp
  have hw'z : w' ≠ zT := by
    intro h
    rw [hw', hzT, twW, twZ, twMk, twMk, mk_eq_mk_iff_twist nativeType hζ hζc' hζ2] at h
    rcases h with h | h
    · exact hw0t (congrArg (fun x : fibreProd nativeType.φ π => x.1.1) h).symm
    · exact hζ1 (by
        have := congrArg (fun x : fibreProd nativeType.φ π => x.1.2) h
        simpa [zζ] using this.symm)
  have hσz : σ S.zM = zT := map_zM_eq S σ hzTc hzT1
  set w := σ.symm w' with hwdef
  have hσw : σ w = w' := σ.apply_symm_apply w'
  have hwQ : (w : G) ∈ S.QG := by
    have hN : ((twTau hζ).ker.map σ.symm.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ σ.symm.surjective
    have hP : IsPGroup 2 ((twTau hζ).ker.map σ.symm.toMonoidHom) :=
      (isPGroup_ker_twTau hζ hker hζ2).map _
    have hle := S.le_of_normal _ hN hP
    have hwk : w' ∈ (twTau hζ).ker := by
      rw [MonoidHom.mem_ker, hw', twW, twMk]
      exact hw₀
    exact ⟨w, hle ⟨w', hwk, rfl⟩, rfl⟩
  have hw2 : orderOf (w : G) = 2 := by
    rw [Subgroup.orderOf_coe, hwdef, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact hw'2) hw'1
  have hwz : (w : G) ≠ S.z := fun h => hw'z (by
    rw [← hσw, ← hσz]
    exact congrArg σ (Subtype.ext h))
  have h5 : 5 ≤ finrank (ZMod 2) S.Qt := by rw [S.finrank_Qt_eq_two_mul_width, hw]; norm_num
  have hswap := card_sq_eq_of_mulEquiv S h5 hΩ hNWC σ hwQ hw2 hwz
  rw [hσw, hσz] at hswap
  have hlow := card_twist_sq_z_ge nativeType hζ hζc' hζ2 hζ1 hπ hker hw₀
  have hup := card_twist_sq_w_le nativeType hζ hζc' hζ2 hζ1 hπ hker hw₀
  rw [← hw', ← hzT] at hlow
  rw [← hw'] at hup
  have h1200 := card_sq_one_ge
  have h480 := card_sq_w_le
  have hmono : Nat.card {h : ↥(invE 1) // h * w0C = w0C * h ∧ h * h = 1 ∧
      ∃ γ : Lm, phi0 h * γ = γ * lB} ≤
      Nat.card {h : ↥(invE 1) // h * w0C = w0C * h ∧ h * h = 1 ∧
        ∀ e, π e = nativeType.φ h → e * e = ζ} :=
    card_subtype_mono fun h ⟨hc, hs, γ, hγ⟩ => ⟨hc, hs, fun e he =>
      sq_eq_of_conj hE π hπ hζc hker hζ1 (by rw [he]; exact hγ)⟩
  have hz' : nativeType.z = t1C := rfl
  rw [hz'] at hup
  omega

theorem isPerfect_Lm : Group.IsPerfect Lm := by
  refine ⟨Subgroup.map_injective Lm.subtype_injective ?_⟩
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype, SuzB0.omega_commutator SuzB0.b0_parts.2.2.2.2.2.2]

theorem nonempty_mulEquiv_invE
    (hw : S.width = 3)
    (hE : ¬ ∃ U : Subgroup G, U ≤ S.QG ∧ IsElemAbelian 2 U ∧ Nat.card U = 16)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hNWC : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) :
    Nonempty (S.M ≃* invE 1) := by
  obtain ⟨Gl⟩ := exists_glue nondeg_bilM.exists_eq_one nativeType (Setting.typeSystem S hw hE hΩ)
  have := isPerfect_Lm
  rcases split_or_perfect Gl.π (Gl.π_surj nondeg_bilM) (fun _ => Gl.π_eq_one_iff) with
    ⟨K, hζK, hK⟩ | hperf
  · obtain ⟨e⟩ := exists_mulEquiv_of_split nondeg_bilM Gl K hζK hK
    exact ⟨e.symm⟩
  · obtain ⟨σ⟩ := nonempty_mulEquiv_twist nondeg_bilM Gl
    exact (false_of_twist S hw hΩ hNWC hperf Gl.π (Gl.π_surj nondeg_bilM) Gl.ζ_mem_center
      (fun _ => Gl.π_eq_one_iff) Gl.ζ_ne_one Gl.π_ζ σ).elim

end CFSG.Sporadic.SuzRecog
