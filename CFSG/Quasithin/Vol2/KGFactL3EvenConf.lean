module

public import CFSG.Quasithin.Vol2.KGFactL3EvenMat

public section

namespace CFSG.Quasithin.H13.KGL3Even

open Matrix CFSG.Quasithin.H13.Ch4.KGSL3 CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Conf

variable {G G' : Type*} [Group G] [Group G']

structure LConf (R K : Subgroup G) : Prop where
  le_normalizer : K ≤ Subgroup.normalizer (R : Set G)
  normalizer_le : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (K : Set G)
  core : ∀ N : Subgroup G, N ≤ K → K ≤ Subgroup.normalizer (N : Set G) → IsPGroup 2 N → N ≤ R

@[expose] def Comm2 (K : Subgroup G) : Prop :=
  ∀ a ∈ ⁅⁅K, K⁆, ⁅K, K⁆⁆, ∀ b ∈ ⁅⁅K, K⁆, ⁅K, K⁆⁆, a * b = b * a

theorem map_map_symm (φ : G ≃* G') (H : Subgroup G) :
    (H.map φ.toMonoidHom).map φ.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem LConf.map {R K : Subgroup G} (h : LConf R K) (φ : G ≃* G') :
    LConf (R.map φ.toMonoidHom) (K.map φ.toMonoidHom) where
  le_normalizer := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono h.le_normalizer
  normalizer_le := by
    rw [← Subgroup.map_equiv_normalizer_eq, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono h.normalizer_le
  core := by
    intro N hNK hKN hN2
    have h1 : N.map φ.symm.toMonoidHom ≤ K := by
      have := Subgroup.map_mono (f := φ.symm.toMonoidHom) hNK
      rwa [map_map_symm] at this
    have h2 : K ≤ Subgroup.normalizer ((N.map φ.symm.toMonoidHom : Subgroup G) : Set G) := by
      have := Subgroup.map_mono (f := φ.symm.toMonoidHom) hKN
      rwa [map_map_symm, Subgroup.map_equiv_normalizer_eq] at this
    have h3 := h.core _ h1 h2 (hN2.map _)
    have := Subgroup.map_mono (f := φ.toMonoidHom) h3
    have e := map_map_symm φ.symm N
    rw [MulEquiv.symm_symm] at e
    rwa [e] at this

theorem Comm2.of_map {K : Subgroup G} (φ : G ≃* G') (h : Comm2 (K.map φ.toMonoidHom)) :
    Comm2 K := by
  intro a ha b hb
  have hmap : ∀ x ∈ ⁅⁅K, K⁆, ⁅K, K⁆⁆, φ x ∈ ⁅⁅K.map φ.toMonoidHom, K.map φ.toMonoidHom⁆,
      ⁅K.map φ.toMonoidHom, K.map φ.toMonoidHom⁆⁆ := by
    intro x hx
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
    exact ⟨x, hx, rfl⟩
  apply φ.injective
  rw [map_mul, map_mul]
  exact h _ (hmap a ha) _ (hmap b hb)

theorem Comm2.map {K : Subgroup G} (h : Comm2 K) (f : G →* G') : Comm2 (K.map f) := by
  rw [Comm2, ← Subgroup.map_commutator, ← Subgroup.map_commutator]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, h a ha b hb]

theorem not_comm2_of_perfect {K : Subgroup G} (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) : ¬ Comm2 K := by
  intro h
  rw [Comm2, hK, hK] at h
  apply hK1
  rw [← hK, eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact h a ha b hb

theorem lconf_subgroupOf {S R K : Subgroup G} (hRS : R ≤ S) (hKS : K ≤ S)
    (hKR : K ≤ Subgroup.normalizer (R : Set G))
    (hRK : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hcore : ∀ N : Subgroup G, N ≤ K → K ≤ Subgroup.normalizer (N : Set G) → IsPGroup 2 N →
      N ≤ R) :
    LConf (R.subgroupOf S) (K.subgroupOf S) where
  le_normalizer := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have hkN := hKR (Subgroup.mem_subgroupOf.mp hk)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hkN s
  normalizer_le := by
    intro s hs
    have hsX : (s : G) ∈ Subgroup.normalizer (R : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      by_cases hx : x ∈ S
      · have := Subgroup.mem_normalizer_iff.mp hs ⟨x, hx⟩
        simpa [Subgroup.mem_subgroupOf] using this
      · have h1 : x ∉ R := fun h => hx (hRS h)
        have h2 : (s : G) * x * (s : G)⁻¹ ∉ R := by
          intro h
          apply hx
          have := hRS h
          have e : x = (s : G)⁻¹ * ((s : G) * x * (s : G)⁻¹) * s := by group
          rw [e]
          exact S.mul_mem (S.mul_mem (S.inv_mem s.2) this) s.2
        exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    have hsK := hRK hsX
    rw [Subgroup.mem_normalizer_iff]
    intro t
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hsK t
  core := by
    intro N hNK hKN hN2
    have h1 : N.map S.subtype ≤ K := by
      rintro _ ⟨n, hn, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hNK hn)
    have h2 : K ≤ Subgroup.normalizer ((N.map S.subtype : Subgroup G) : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hkS : (⟨k, hKS hk⟩ : ↥S) ∈ K.subgroupOf S := hk
      have hkN := Subgroup.mem_normalizer_iff.mp (hKN hkS)
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨_, (hkN n).mp hn, rfl⟩
      · rintro ⟨n, hn, hne⟩
        have hxS : x ∈ S := by
          have e : x = k⁻¹ * (k * x * k⁻¹) * k := by group
          rw [e, ← hne]
          exact S.mul_mem (S.mul_mem (S.inv_mem (hKS hk)) n.2) (hKS hk)
        refine ⟨⟨x, hxS⟩, (hkN ⟨x, hxS⟩).mpr ?_, rfl⟩
        have : (⟨k, hKS hk⟩ : ↥S) * ⟨x, hxS⟩ * (⟨k, hKS hk⟩ : ↥S)⁻¹ = n := Subtype.ext hne.symm
        rw [this]
        exact hn
    have h3 := hcore _ h1 h2 (hN2.map S.subtype)
    intro n hn
    exact Subgroup.mem_subgroupOf.mpr (h3 ⟨n, hn, rfl⟩)

end Conf

variable {F : Type} [Field F]

theorem card_uSub [Finite F] :
    Nat.card (uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) = Nat.card F ^ 2 := by
  have e : (Fin 2 → F) ≃ (uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) :=
    Equiv.ofBijective (fun c => ⟨uOf c, uOf_mem c⟩)
      ⟨fun c d h => uOf_injective (congrArg Subtype.val h), by
        rintro ⟨_, c₀, c₁, rfl⟩
        exact ⟨![c₀, c₁], Subtype.ext (by simp [uOf])⟩⟩
  rw [← Nat.card_congr e, Nat.card_fun, Nat.card_fin]

theorem unitri_case [CharP F 2] {R₀ K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hc : LConf R₀ K) (hR : R₀ ≤ unitriangular 3 F) (hR1 : R₀ ≠ ⊥)
    (hsq : ∀ r ∈ R₀, r * r = 1) (hcomm : ∀ r ∈ R₀, ∀ s ∈ R₀, r * s = s * r) :
    R₀ = uSub ∨ R₀.map theta.toMonoidHom = uSub ∨ Comm2 K := by
  rcases le_uSub_or_le_vSub hR hsq hcomm with h | h
  · have hRU : R₀ ≤ uSub := fun r hr => ⟨_, _, eq_uSL_of_unitri (hR hr) (h r hr)⟩
    rcases plane_case hRU hR1 hc.le_normalizer hc.normalizer_le hc.core with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')
  · have hRU : R₀.map theta.toMonoidHom ≤ uSub := by
      rintro _ ⟨r, hr, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, eq_vSL_of_unitri (hR hr) (h r hr), theta_vSL]
      exact ⟨_, _, rfl⟩
    have hR1' : R₀.map theta.toMonoidHom ≠ ⊥ := by
      intro hb
      apply hR1
      rw [← map_map_symm theta R₀, hb, Subgroup.map_bot]
    have hc' := hc.map theta
    rcases plane_case hRU hR1' hc'.le_normalizer hc'.normalizer_le hc'.core with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Comm2.of_map theta h'))

theorem pow_three_of_mem_scalars {z : SpecialLinearGroup (Fin 3) F} (hz : z ∈ scalars 3 F) :
    z ^ 3 = 1 := by
  obtain ⟨c, hc, hz⟩ := hz
  apply Subtype.ext
  change (z : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  rw [hz, ← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]

theorem mem_unitriangular_of_pow {x : SpecialLinearGroup (Fin 3) F}
    (hx : proj 3 F x ∈ projUnitriangular 3 F) {m : ℕ} (hm : x ^ (2 ^ m) = 1) :
    x ∈ unitriangular 3 F := by
  obtain ⟨t, ht, hπ⟩ := hx
  have hz : t⁻¹ * x ∈ scalars 3 F := proj_eq_proj_iff.mp hπ
  set z := t⁻¹ * x with hzdef
  have hxz : x = t * z := by rw [hzdef]; group
  have hzc : ∀ y, z * y = y * z := fun y =>
    (Subgroup.mem_center_iff.mp (scalars_le_center 3 F hz) y).symm
  have hpow : z ^ (2 ^ m) = (t ^ (2 ^ m))⁻¹ := by
    have h1 : x ^ (2 ^ m) = t ^ (2 ^ m) * z ^ (2 ^ m) := by
      rw [hxz]
      exact (Commute.mul_pow (Commute.symm (hzc t)) _)
    rw [hm] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hmem : z ^ (2 ^ m) ∈ unitriangular 3 F ⊓ scalars 3 F :=
    ⟨hpow ▸ (unitriangular 3 F).inv_mem ((unitriangular 3 F).pow_mem ht _),
      (scalars 3 F).pow_mem hz _⟩
  rw [unitriangular_inf_scalars, Subgroup.mem_bot] at hmem
  have h3 := pow_three_of_mem_scalars hz
  have hz1 : z = 1 := by
    have hd : orderOf z ∣ Nat.gcd (2 ^ m) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hmem) (orderOf_dvd_of_pow_eq_one h3)
    have hg : Nat.gcd (2 ^ m) 3 = 1 :=
      Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 3)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  rw [hxz, hz1, mul_one]
  exact ht

theorem exists_pow_eq_one {H : Subgroup (SpecialLinearGroup (Fin 3) F)} (hH : IsPGroup 2 H)
    {x : SpecialLinearGroup (Fin 3) F} (hx : x ∈ H) : ∃ m : ℕ, x ^ (2 ^ m) = 1 := by
  obtain ⟨m, hm⟩ := hH ⟨x, hx⟩
  exact ⟨m, congrArg Subtype.val hm⟩

theorem isPGroup_unitriangular [Finite F] [CharP F 2] : IsPGroup 2 (unitriangular 3 F) := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← hP]
  exact P.isPGroup'

theorem lconf_lift [Finite F] [CharP F 2] {R K : Subgroup (projectiveSL 3 F)} (hc : LConf R K)
    (hR : R ≤ projUnitriangular 3 F) :
    LConf (R.comap (proj 3 F) ⊓ unitriangular 3 F) (K.comap (proj 3 F)) ∧
      (R.comap (proj 3 F) ⊓ unitriangular 3 F).map (proj 3 F) = R ∧
      (K.comap (proj 3 F)).map (proj 3 F) = K := by
  set R₀ := R.comap (proj 3 F) ⊓ unitriangular 3 F with hR₀
  have hU2 : IsPGroup 2 (unitriangular 3 F) := isPGroup_unitriangular
  have hmapR : R₀.map (proj 3 F) = R := by
    refine le_antisymm ?_ fun r hr => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · obtain ⟨t, ht, hπ⟩ := hR hr
      exact ⟨t, Subgroup.mem_inf.mpr ⟨show proj 3 F t ∈ R by rw [hπ]; exact hr, ht⟩, hπ⟩
  have hmapK : (K.comap (proj 3 F)).map (proj 3 F) = K :=
    Subgroup.map_comap_eq_self_of_surjective (proj_surjective 3 F) K
  have h2el : ∀ x, proj 3 F x ∈ R → ∀ m : ℕ, x ^ (2 ^ m) = 1 → x ∈ R₀ :=
    fun x hx m hm => ⟨hx, mem_unitriangular_of_pow (hR hx) hm⟩
  refine ⟨⟨?_, ?_, ?_⟩, hmapR, hmapK⟩
  · intro k hk
    rw [Subgroup.mem_normalizer_iff]
    have hkN := hc.le_normalizer hk
    intro r
    constructor
    · intro hr
      obtain ⟨m, hm⟩ := exists_pow_eq_one (hU2.to_le inf_le_right) hr
      refine h2el _ ?_ m ?_
      · rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hkN _).mp (Subgroup.mem_inf.mp hr).1
      · rw [conj_pow, hm, mul_one, mul_inv_cancel]
    · intro hr
      obtain ⟨m, hm⟩ := exists_pow_eq_one (hU2.to_le inf_le_right) hr
      refine h2el _ ?_ m ?_
      · have h1 : proj 3 F (k * r * k⁻¹) ∈ R := (Subgroup.mem_inf.mp hr).1
        rw [map_mul, map_mul, map_inv] at h1
        exact (Subgroup.mem_normalizer_iff.mp hkN _).mpr h1
      · rw [conj_pow, mul_inv_eq_one, mul_eq_left] at hm
        exact hm
  · intro g hg
    have h1 : proj 3 F g ∈ Subgroup.normalizer (R : Set (projectiveSL 3 F)) := by
      rw [← hmapR]
      exact Subgroup.le_normalizer_map _ ⟨g, hg, rfl⟩
    have h2 := hc.normalizer_le h1
    rw [← Subgroup.comap_normalizer_eq_of_surjective _ (proj_surjective 3 F)]
    exact h2
  · intro N hNK hKN hN2
    have hπN : N.map (proj 3 F) ≤ R := by
      refine hc.core _ ?_ ?_ (hN2.map _)
      · rintro _ ⟨n, hn, rfl⟩
        exact hNK hn
      · rw [← hmapK]
        exact (Subgroup.map_mono hKN).trans (Subgroup.le_normalizer_map _)
    intro n hn
    obtain ⟨m, hm⟩ := exists_pow_eq_one hN2 hn
    exact h2el n (hπN ⟨n, hn, rfl⟩) m hm

theorem lift_props [Finite F] {R : Subgroup (projectiveSL 3 F)} :
    Nat.card ↥(R.comap (proj 3 F) ⊓ unitriangular 3 F) =
      Nat.card ↥((R.comap (proj 3 F) ⊓ unitriangular 3 F).map (proj 3 F)) ∧
    ((∀ r ∈ R, r * r = 1) → ∀ r ∈ R.comap (proj 3 F) ⊓ unitriangular 3 F, r * r = 1) ∧
    ((∀ r ∈ R, ∀ s ∈ R, r * s = s * r) → ∀ r ∈ R.comap (proj 3 F) ⊓ unitriangular 3 F,
      ∀ s ∈ R.comap (proj 3 F) ⊓ unitriangular 3 F, r * s = s * r) := by
  have hinj : ∀ a ∈ unitriangular 3 F, ∀ b ∈ unitriangular 3 F, proj 3 F a = proj 3 F b →
      a = b := fun a ha b hb h => proj_injOn_unitriangular 3 ha hb h
  refine ⟨?_, ?_, ?_⟩
  · refine (Nat.card_congr (Equiv.ofBijective
      (fun x : ↥(R.comap (proj 3 F) ⊓ unitriangular 3 F) =>
        (⟨proj 3 F x, ⟨x, x.2, rfl⟩⟩ :
          ↥((R.comap (proj 3 F) ⊓ unitriangular 3 F).map (proj 3 F)))) ⟨?_, ?_⟩))
    · intro x y h
      exact Subtype.ext (hinj _ x.2.2 _ y.2.2 (congrArg Subtype.val h))
    · rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  · intro h r hr
    refine hinj _ ((unitriangular 3 F).mul_mem hr.2 hr.2) _ (unitriangular 3 F).one_mem ?_
    rw [map_mul, map_one]
    exact h _ hr.1
  · intro h r hr s hs
    refine hinj _ ((unitriangular 3 F).mul_mem hr.2 hs.2) _
      ((unitriangular 3 F).mul_mem hs.2 hr.2) ?_
    rw [map_mul, map_mul]
    exact h _ hr.1 _ hs.1

theorem exists_conj_le [Finite F] [CharP F 2] {R : Subgroup (projectiveSL 3 F)}
    (hR : IsPGroup 2 R) : ∃ g : projectiveSL 3 F,
      R.map (MulAut.conj g).toMonoidHom ≤ projUnitriangular 3 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨Q', hRQ'⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 F) Q' Q
  refine ⟨g, ?_⟩
  rw [← hQ, ← hg]
  exact Subgroup.map_mono hRQ'

end CFSG.Quasithin.H13.KGL3Even
