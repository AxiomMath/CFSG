module

public import CFSG.Quasithin.Recognition.J2RecTwoBCent

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv CFSG.LieType.BorelTits J2Cz J2Cz.QM

theorem J2Cz.eq_one_of_comm_pa_pb : ∀ σ : Perm (Fin 5), σ * pa = pa * σ → σ * pb = pb * σ →
    σ = 1 := by
  decide +kernel

theorem J2Cz.QM.eq_of_phiAHom_phiBHom : ∀ p : QM, phiAHom p = p → phiBHom p = p →
    p = 1 ∨ p = z := by
  decide +kernel

theorem J2Cz.orders_of_pa : ∀ γ : Perm (Fin 5), γ * γ = 1 → (pa * γ) ^ 5 = 1 → pa * γ ≠ 1 →
    ((γ * pc) ^ 3 = 1 ∧ (γ * (pa * pc)) ^ 5 = 1) ∨
      ((γ * pc) ^ 5 = 1 ∧ (γ * (pa * pc)) ^ 3 = 1) := by
  decide +kernel

theorem J2Cz.QM.x_mul_x_sq : ∀ i j : Fin 5, i ≠ j → (x i * x j) ^ 2 = z := by decide +kernel

theorem J2Cz.QM.zx_mul_self : ∀ j : Fin 5,
    z * x (swap (0 : Fin 5) 1 j) * (z * x (swap (0 : Fin 5) 1 j)) = 1 := by
  decide +kernel

theorem J2Cz.QM.zx_mul_zx_sq : ∀ i j : Fin 5, i ≠ j →
    (z * x (swap (0 : Fin 5) 1 i) * (z * x (swap (0 : Fin 5) 1 j))) ^ 2 = z := by
  decide +kernel

theorem J2Cz.QM.zx_prod : z * x (swap (0 : Fin 5) 1 0) * (z * x (swap (0 : Fin 5) 1 1)) *
    (z * x (swap (0 : Fin 5) 1 2)) * (z * x (swap (0 : Fin 5) 1 3)) *
      (z * x (swap (0 : Fin 5) 1 4)) = 1 := by
  decide +kernel

theorem conj_eq_inv_of_centralizer {G : Type*} [Group G] [Finite G] {Y : Subgroup G} {z : G}
    (hzY : z ∈ Y) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hC : ∀ g ∈ Y, g * z = z * g → g = 1 ∨ g = z) {f : G} (hfY : f ∈ Y) (hf : f * f ≠ 1) :
    z * f * z = f⁻¹ := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hfz : f * z ≠ z * f := fun h1 => by
    rcases hC f hfY h1 with h2 | h2
    · rw [h2] at hf
      exact hf (one_mul 1)
    · rw [h2] at hf
      exact hf hz2
  set z' := f * z * f⁻¹ with hz'
  have hz'2 : z' * z' = 1 := by
    rw [hz']
    calc f * z * f⁻¹ * (f * z * f⁻¹) = f * (z * z) * f⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hz'i : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
  set d := z * z' with hd
  have hdY : d ∈ Y := Y.mul_mem hzY (Y.mul_mem (Y.mul_mem hfY hzY) (Y.inv_mem hfY))
  have hzd1 : z * d * z = d⁻¹ := by
    rw [hd, mul_inv_rev, hz'i, hzi, ← mul_assoc z z, hz2, one_mul]
  have hzd : ∀ j : ℕ, z * d ^ j * z = (d ^ j)⁻¹ := by
    intro j
    calc z * d ^ j * z = z * d ^ j * z⁻¹ := by rw [hzi]
      _ = (z * d * z⁻¹) ^ j := by rw [conj_pow]
      _ = (d⁻¹) ^ j := by rw [hzi, hzd1]
      _ = (d ^ j)⁻¹ := by rw [inv_pow]
  have hk0 : 0 < orderOf d := orderOf_pos d
  obtain ⟨r, hr⟩ : ∃ r, orderOf d = 2 * r + 1 := by
    rcases Nat.even_or_odd (orderOf d) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exfalso
      have hr0 : r ≠ 0 := by omega
      have hw1 : d ^ r ≠ 1 := pow_ne_one_of_lt_orderOf hr0 (by omega)
      have hw2 : d ^ r * d ^ r = 1 := by rw [← pow_add, ← hr, pow_orderOf_eq_one]
      have hwz : d ^ r * z = z * d ^ r := by
        have h1 := hzd r
        rw [inv_eq_of_mul_eq_one_right hw2] at h1
        calc d ^ r * z = z * d ^ r * z * z := by rw [h1]
          _ = z * d ^ r := by rw [mul_assoc (z * d ^ r), hz2, mul_one]
      rcases hC _ (Y.pow_mem hdY r) hwz with h2 | h2
      · exact hw1 h2
      · have hdz : d * z = z * d := by
          rw [← h2]
          exact (Commute.self_pow d r).eq
        rcases hC d hdY hdz with h3 | h3
        · apply hfz
          have h4 : z' = z := by
            calc z' = z⁻¹ * d := by rw [hd]; group
              _ = z := by rw [h3, mul_one, hzi]
          calc f * z = f * z * f⁻¹ * f := by group
            _ = z * f := by rw [← hz', h4]
        · apply hz1
          have h4 : z' = 1 := by
            calc z' = z⁻¹ * d := by rw [hd]; group
              _ = 1 := by rw [h3, inv_mul_cancel]
          calc z = f⁻¹ * z' * f := by rw [hz']; group
            _ = 1 := by rw [h4]; group
    · exact ⟨r, hr⟩
  set e := d ^ r with he
  have hdk : d ^ (2 * r + 1) = 1 := by rw [← hr, pow_orderOf_eq_one]
  have hee : e * e * d = 1 := by
    rw [he, ← pow_add, ← pow_succ, ← two_mul, hdk]
  have h2 : e⁻¹ * e⁻¹ = d := by
    calc e⁻¹ * e⁻¹ = e⁻¹ * e⁻¹ * (e * e * d) := by rw [hee, mul_one]
      _ = d := by group
  have hez : e * z * e⁻¹ = z' := by
    have h1 : z * e * z = e⁻¹ := hzd r
    calc e * z * e⁻¹ = z * (z * e * z) * e⁻¹ := by
          rw [show z * (z * e * z) * e⁻¹ = (z * z) * (e * z * e⁻¹) by group, hz2, one_mul]
      _ = z * (e⁻¹ * e⁻¹) := by rw [h1]; group
      _ = z * d := by rw [h2]
      _ = z' := by rw [hd, ← mul_assoc, hz2, one_mul]
  have hfe : f⁻¹ * e * z = z * (f⁻¹ * e) := by
    calc f⁻¹ * e * z = f⁻¹ * (e * z * e⁻¹) * e := by group
      _ = f⁻¹ * (f * z * f⁻¹) * e := by rw [hez]
      _ = z * (f⁻¹ * e) := by group
  rcases hC _ (Y.mul_mem (Y.inv_mem hfY) (Y.pow_mem hdY r)) hfe with h3 | h3
  · have hfe' : f = e := by
      calc f = f * (f⁻¹ * e) := by rw [h3, mul_one]
        _ = e := by group
    rw [hfe']
    exact hzd r
  · exfalso
    apply hf
    have hfe' : f = e * z := by
      calc f = f * (f⁻¹ * e) * z⁻¹ := by rw [h3, mul_inv_cancel_right]
        _ = e * z := by rw [hzi]; group
    rw [hfe']
    calc e * z * (e * z) = e * (z * e * z) := by group
      _ = 1 := by rw [hzd r, mul_inv_cancel]

namespace J2Frame

variable {G : Type} [Group G] {z : G} (F : J2Frame G z)

theorem czAct_ι_pb (h : F.ι ⟨pb, pb_mem⟩ ∈ Subgroup.centralizer ({z} : Set G)) :
    IsTypeH2.czAct F.χ ⟨F.ι ⟨pb, pb_mem⟩, h⟩ = phiB :=
  eq_of_linePerm_eq (F.act_mem _ (F.ι_mem _)) phiB_mem
    ((F.linePerm_czAct_ι _ h).trans linePerm_phiB.symm)

theorem eq_one_or_eq_of_comm_L {g : G} (hgH : g ∈ Subgroup.centralizer ({z} : Set G))
    (hgL : ∀ l ∈ F.L, g * l = l * g) : g = 1 ∨ g = z := by
  set gH : ↥(Subgroup.centralizer ({z} : Set G)) := ⟨g, hgH⟩ with hgH'
  have hperm : ∀ σ : alternatingGroup (Fin 5),
      linePerm (IsTypeH2.czAct F.χ gH) * σ = σ * linePerm (IsTypeH2.czAct F.χ gH) := by
    intro σ
    have h1 : gH * ⟨F.ι σ, F.ι_mem_centralizer σ⟩ = ⟨F.ι σ, F.ι_mem_centralizer σ⟩ * gH :=
      Subtype.ext (hgL _ (F.ι_mem σ))
    have h2 := congrArg (fun k => linePermHom (IsTypeH2.czAct F.χ k)) h1
    simp only [map_mul, linePermHom_apply, F.linePerm_czAct_ι] at h2
    exact h2
  have h1 : linePerm (IsTypeH2.czAct F.χ gH) = 1 :=
    eq_one_of_comm_pa_pb _ (hperm ⟨pa, pa_mem⟩) (hperm ⟨pb, pb_mem⟩)
  have hgQ := F.isTypeH2.mem_pCoreOf_of_linePerm_eq_one F.χ h1
  obtain ⟨p, hp⟩ := F.exists_emb_eq hgQ
  have hfix : ∀ (σ : alternatingGroup (Fin 5)) (hσ : F.ι σ ∈ Subgroup.centralizer ({z} : Set G)),
      IsTypeH2.czAct F.χ ⟨F.ι σ, hσ⟩ p = p := by
    intro σ hσ
    apply F.emb_injective
    rw [← F.conj_emb]
    show F.ι σ * F.emb p * (F.ι σ)⁻¹ = F.emb p
    rw [hp, ← hgL _ (F.ι_mem σ), mul_inv_cancel_right]
  have hA : phiAHom p = p := by
    have h2 := hfix ⟨pa, pa_mem⟩ (F.ι_mem_centralizer _)
    rw [F.czAct_ι, lineEquiv_symm_pa] at h2
    exact h2
  have hB : phiBHom p = p := by
    have h2 := hfix ⟨pb, pb_mem⟩ (F.ι_mem_centralizer _)
    rw [F.czAct_ι_pb] at h2
    exact h2
  rcases eq_of_phiAHom_phiBHom p hA hB with rfl | rfl
  · exact Or.inl (hp.symm.trans (map_one _))
  · exact Or.inr (hp.symm.trans F.emb_z)

variable [Finite G]

theorem exists_mem_centralizer_L (h5 : 5 ∣ Nat.card (Subgroup.centralizer (F.L : Set G))) :
    ∃ f ∈ Subgroup.centralizer (F.L : Set G), f ^ 5 = 1 ∧ f ≠ 1 ∧ z * f * z = f⁻¹ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hf' : orderOf (f : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hf
  have hf5 : (f : G) ^ 5 = 1 := by rw [← hf']; exact pow_orderOf_eq_one _
  have hf1 : (f : G) ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hf'; norm_num at hf'
  have hzz : z * z = 1 := by rw [← pow_two]; exact F.isTypeH2.sq
  have hzY : z ∈ Subgroup.centralizer (F.L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (F.le hl)
  have hC : ∀ g ∈ Subgroup.centralizer (F.L : Set G), g * z = z * g → g = 1 ∨ g = z := by
    intro g hg hgz
    refine F.eq_one_or_eq_of_comm_L (Subgroup.mem_centralizer_singleton_iff.mpr hgz) fun l hl => ?_
    exact ((Subgroup.mem_centralizer_iff.mp hg) l hl).symm
  have hff : (f : G) * f ≠ 1 := by
    intro h1
    apply hf1
    calc (f : G) = (f : G) ^ 5 * ((f : G) * f)⁻¹ * ((f : G) * f)⁻¹ := by group
      _ = 1 := by rw [hf5, h1]; group
  exact ⟨f, f.2, hf5, hf1,
    conj_eq_inv_of_centralizer hzY hzz F.isTypeH2.ne_one hC f.2 hff⟩

theorem orders_pt_four (hcount : involutionClassCount G = 2) {c : G} (hcM : c ∈ F.M hcount)
    (hc2 : c * c = 1) (hzc5 : (z * c) ^ 5 = 1) (hzc1 : z * c ≠ 1)
    (e : ↥(F.M hcount) ≃* alternatingGroup (Fin 5)) :
    ((c * F.pt 4) ^ 3 = 1 ∧ (c * (z * F.pt 4)) ^ 5 = 1) ∨
      ((c * F.pt 4) ^ 5 = 1 ∧ (c * (z * F.pt 4)) ^ 3 = 1) := by
  have hzM := F.W_le_M hcount F.z_mem_W
  have hx4M := F.W_le_M hcount F.pt_four_mem_W
  set zM : ↥(F.M hcount) := ⟨z, hzM⟩ with hzM'
  set xM : ↥(F.M hcount) := ⟨F.pt 4, hx4M⟩ with hxM'
  set cM : ↥(F.M hcount) := ⟨c, hcM⟩ with hcM'
  set ψ₀ : ↥(F.M hcount) →* Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp e.toMonoidHom
    with hψ₀'
  have hψ₀ : Function.Injective ψ₀ := Subtype.val_injective.comp e.injective
  have hψ₀sign : ∀ y, Perm.sign (ψ₀ y) = 1 := fun y => Perm.mem_alternatingGroup.mp (e y).2
  have hz2M : zM * zM = 1 := Subtype.ext (F.mul_self_of_mem_W F.z_mem_W)
  have hz1M : zM ≠ 1 := fun h1 => F.isTypeH2.ne_one (congrArg Subtype.val h1)
  obtain ⟨π, hπ, hπz⟩ := exists_conj_pa (ψ₀ zM) (hψ₀sign zM)
    (by rw [← map_mul, hz2M, map_one]) (fun h1 => hz1M (hψ₀ (h1.trans (map_one ψ₀).symm)))
  set ψ : ↥(F.M hcount) →* Perm (Fin 5) := (MulAut.conj π).toMonoidHom.comp ψ₀ with hψ'
  have hψ : Function.Injective ψ := (MulAut.conj π).injective.comp hψ₀
  have hψapp : ∀ y, ψ y = π * ψ₀ y * π⁻¹ := fun y => rfl
  have hψz : ψ zM = pa := by rw [hψapp]; exact hπz
  have hψsign : ∀ y, Perm.sign (ψ y) = 1 := by
    intro y
    rw [hψapp, map_mul, map_mul, map_inv, hπ, hψ₀sign, inv_one, mul_one, one_mul]
  have hxz : xM * zM = zM * xM := Subtype.ext (F.comm_of_mem_W F.pt_four_mem_W F.z_mem_W)
  have hβ : ψ xM * pa = pa * ψ xM := by rw [← hψz, ← map_mul, ← map_mul, hxz]
  have hβ1 : ψ xM ≠ 1 := fun h1 => by
    have h2 := hψ (h1.trans (map_one ψ).symm)
    exact x_ne_one 4 (F.emb_injective ((congrArg Subtype.val h2).trans (map_one F.emb).symm))
  have hβa : ψ xM ≠ pa := fun h1 => by
    have h2 := hψ (h1.trans hψz.symm)
    exact x_ne_z 4 (F.emb_injective ((congrArg Subtype.val h2).trans F.emb_z.symm))
  have hβ' : ψ xM = pc ∨ ψ xM = pa * pc := by
    rcases eq_of_comm_pa (ψ xM) hβ (hψsign xM) with h1 | h1 | h1 | h1
    · exact absurd h1 hβ1
    · exact absurd h1 hβa
    · exact Or.inl h1
    · exact Or.inr h1
  have hγ2 : ψ cM * ψ cM = 1 := by
    rw [← map_mul, show cM * cM = 1 from Subtype.ext hc2, map_one]
  have hγ5 : (pa * ψ cM) ^ 5 = 1 := by
    rw [← hψz, ← map_mul, ← map_pow, show (zM * cM) ^ 5 = 1 from Subtype.ext (by simpa using hzc5),
      map_one]
  have hγ1 : pa * ψ cM ≠ 1 := fun h1 => by
    have h2 : ψ (zM * cM) = ψ 1 := by rw [map_mul, hψz, h1, map_one]
    exact hzc1 (congrArg Subtype.val (hψ h2))
  have hord := orders_of_pa (ψ cM) hγ2 hγ5 hγ1
  have key : ∀ (y : ↥(F.M hcount)) (n : ℕ), (y : G) ^ n = 1 ↔ (ψ y) ^ n = 1 := by
    intro y n
    constructor
    · intro h1
      rw [← map_pow, show y ^ n = 1 from Subtype.ext (by simpa using h1), map_one]
    · intro h1
      have h2 : ψ (y ^ n) = ψ 1 := by rw [map_pow, h1, map_one]
      simpa using congrArg Subtype.val (hψ h2)
  have e1 : c * F.pt 4 = ((cM * xM : ↥(F.M hcount)) : G) := rfl
  have e2 : c * (z * F.pt 4) = ((cM * (zM * xM) : ↥(F.M hcount)) : G) := rfl
  rw [e1, e2, key, key, key, key, map_mul, map_mul, map_mul, hψz]
  rcases hβ' with hβ' | hβ'
  · rw [hβ']
    exact hord
  · rw [hβ', show pa * (pa * pc) = pc by rw [← mul_assoc, pa_sq, one_mul]]
    rcases hord with ⟨h3, h5⟩ | ⟨h5, h3⟩
    · exact Or.inr ⟨h5, h3⟩
    · exact Or.inl ⟨h3, h5⟩

omit [Finite G] in
theorem pow_eq_one_of_four {c : G} (hcL : ∀ l ∈ F.L, c * l = l * c) {n : ℕ} {w : G}
    (hw : w = 1 ∨ w = z) (h4 : (c * (w * F.pt 4)) ^ n = 1) (j : Fin 5) :
    (c * (w * F.pt j)) ^ n = 1 := by
  obtain ⟨π, hπ, hπj⟩ := exists_alt_apply_eq 4 j
  set σ : alternatingGroup (Fin 5) := ⟨π, Perm.mem_alternatingGroup.mpr hπ⟩ with hσ
  have hc : F.ι σ * c * (F.ι σ)⁻¹ = c := by
    rw [← hcL _ (F.ι_mem σ), mul_inv_cancel_right]
  have hwι : F.ι σ * w * (F.ι σ)⁻¹ = w := by
    rcases hw with rfl | rfl
    · group
    · rw [F.ι_comm_z, mul_inv_cancel_right]
  have hx : F.ι σ * F.pt 4 * (F.ι σ)⁻¹ = F.pt j := by
    rw [F.ι_conj_pt]
    exact congrArg F.pt hπj
  have e1 : F.ι σ * (c * (w * F.pt 4)) * (F.ι σ)⁻¹ =
      (F.ι σ * c * (F.ι σ)⁻¹) * ((F.ι σ * w * (F.ι σ)⁻¹) * (F.ι σ * F.pt 4 * (F.ι σ)⁻¹)) := by
    group
  rw [hc, hwι, hx] at e1
  rw [← e1, conj_pow, h4, mul_one, mul_inv_cancel]

omit [Finite G] in
theorem z_mul_emb (p : QM) : z * F.emb p = F.emb (J2Cz.QM.z * p) := by rw [map_mul, F.emb_z]

omit [Finite G] in
theorem emb_mul_z (p : QM) : F.emb p * z = F.emb (p * J2Cz.QM.z) := by rw [map_mul, F.emb_z]

omit [Finite G] in
theorem fiveLines_pt : J2FiveLines z F.pt where
  d_sq := by rw [← pow_two]; exact F.isTypeH2.sq
  x_sq i := by
    show F.emb (x i) * F.emb (x i) = 1
    rw [← map_mul, x_sq, map_one]
  d_comm i := by
    show z * F.emb (x i) = F.emb (x i) * z
    rw [F.z_mul_emb, F.emb_mul_z, z_comm]
  sq_eq i j hij := by
    show (F.emb (x i) * F.emb (x j)) ^ 2 = z
    rw [← map_mul, ← map_pow, x_mul_x_sq i j hij, F.emb_z]
  prod_eq := by
    show F.emb (x 0) * F.emb (x 1) * F.emb (x 2) * F.emb (x 3) * F.emb (x 4) = 1
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, x_prod, map_one]

omit [Finite G] in
theorem fiveLines_zpt : J2FiveLines z fun j => z * F.pt (swap (0 : Fin 5) 1 j) where
  d_sq := by rw [← pow_two]; exact F.isTypeH2.sq
  x_sq i := by
    show z * F.emb (x (swap (0 : Fin 5) 1 i)) * (z * F.emb (x (swap (0 : Fin 5) 1 i))) = 1
    rw [F.z_mul_emb, ← map_mul, zx_mul_self, map_one]
  d_comm i := by
    show z * (z * F.emb (x (swap (0 : Fin 5) 1 i))) = z * F.emb (x (swap (0 : Fin 5) 1 i)) * z
    rw [F.z_mul_emb, F.z_mul_emb, F.emb_mul_z, z_comm]
  sq_eq i j hij := by
    show (z * F.emb (x (swap (0 : Fin 5) 1 i)) * (z * F.emb (x (swap (0 : Fin 5) 1 j)))) ^ 2 = z
    rw [F.z_mul_emb, F.z_mul_emb, ← map_mul, ← map_pow, zx_mul_zx_sq i j hij, F.emb_z]
  prod_eq := by
    show z * F.emb (x (swap (0 : Fin 5) 1 0)) * (z * F.emb (x (swap (0 : Fin 5) 1 1))) *
      (z * F.emb (x (swap (0 : Fin 5) 1 2))) * (z * F.emb (x (swap (0 : Fin 5) 1 3))) *
        (z * F.emb (x (swap (0 : Fin 5) 1 4))) = 1
    simp only [F.z_mul_emb, ← map_mul]
    rw [zx_prod, map_one]

omit [Finite G] in
theorem exists_hexagon {c : G} (hcL : ∀ l ∈ F.L, c * l = l * c) (hc2 : c * c = 1)
    (hzc5 : (z * c) ^ 5 = 1) (hzc1 : z * c ≠ 1)
    (hord : ((c * F.pt 4) ^ 3 = 1 ∧ (c * (z * F.pt 4)) ^ 5 = 1) ∨
      ((c * F.pt 4) ^ 5 = 1 ∧ (c * (z * F.pt 4)) ^ 3 = 1)) :
    ∃ x : Fin 5 → G, (∀ i, x i ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ∧
      J2FiveLines z x ∧ J2ClosingRels z c x := by
  have hzz : z * z = 1 := by rw [← pow_two]; exact F.isTypeH2.sq
  have hone : ∀ {n : ℕ}, (c * F.pt 4) ^ n = 1 → ∀ j, (c * F.pt j) ^ n = 1 := by
    intro n h4 j
    have h1 := F.pow_eq_one_of_four hcL (w := 1) (Or.inl rfl) (by simpa using h4) j
    simpa using h1
  have hzed : ∀ {n : ℕ}, (c * (z * F.pt 4)) ^ n = 1 → ∀ j, (c * (z * F.pt j)) ^ n = 1 :=
    fun h4 j => F.pow_eq_one_of_four hcL (Or.inr rfl) h4 j
  rcases hord with ⟨h3, h5⟩ | ⟨h5, h3⟩
  · exact ⟨F.pt, F.pt_mem, F.fiveLines_pt, ⟨hc2, hzc5, hzc1, hone h3, hzed h5⟩⟩
  · refine ⟨fun j => z * F.pt (swap (0 : Fin 5) 1 j),
      fun j => Subgroup.mul_mem _ F.isTypeH2.z_mem_pCoreOf (F.pt_mem _), F.fiveLines_zpt,
      ⟨hc2, hzc5, hzc1, fun i => hzed h3 _, fun i => ?_⟩⟩
    show (c * (z * (z * F.pt (swap (0 : Fin 5) 1 i)))) ^ 5 = 1
    rw [← mul_assoc z z, hzz, one_mul]
    exact hone h5 _

end J2Frame

end CFSG.Quasithin
