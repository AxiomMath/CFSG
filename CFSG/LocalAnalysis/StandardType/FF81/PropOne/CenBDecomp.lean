module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.RExists

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

private abbrev zs0 {G : Type} [Group G] {L : Subgroup G} (z : Fin 3 → ↥L) : G := GGFF.zs z 0

private theorem pow_conj_eq_phi_pow_mul {G : Type} [Group G] {b r φ : G}
    (hcomm : Commute b φ) (hr : b * r * b⁻¹ = φ * r) :
    ∀ i : ℕ, b ^ i * r * (b ^ i)⁻¹ = φ ^ i * r := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have hstep : b ^ (i + 1) * r * (b ^ (i + 1))⁻¹
        = b * (b ^ i * r * (b ^ i)⁻¹) * b⁻¹ := by
      rw [pow_succ']; group
    rw [hstep, ih]
    calc b * (φ ^ i * r) * b⁻¹
        = (b * φ ^ i) * r * b⁻¹ := by group
      _ = (φ ^ i * b) * r * b⁻¹ := by rw [← (hcomm.pow_right i).eq]
      _ = φ ^ i * (b * r * b⁻¹) := by group
      _ = φ ^ i * (φ * r) := by rw [hr]
      _ = φ ^ (i + 1) * r := by rw [pow_succ]; group

private theorem commute_of_mem_zpowers {G : Type} [Group G] [Finite G] {a x : G}
    (h : Commute x a) {g : G} (hg : g ∈ Subgroup.zpowers a) : Commute x g := by
  classical
  obtain ⟨n, -, hn⟩ :=
    Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf (x := a) (y := g)).mp hg)
  rw [← hn]
  exact h.pow_right n

private theorem inf_zpowers_eq_bot_of_not_dvd {G : Type} [Group G] {a : G} {O : Subgroup G}
    (ha : a ^ 3 = 1) (hO : ¬ 3 ∣ Nat.card O) :
    Subgroup.zpowers a ⊓ O = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hga, hgO⟩ := hg
  rw [Subgroup.mem_bot]
  have hdvdO : orderOf g ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hgO
  have hnot3 : ¬ 3 ∣ orderOf g := fun h3 => hO (h3.trans hdvdO)
  have hdvd3 : orderOf g ∣ 3 :=
    (orderOf_dvd_of_mem_zpowers hga).trans (orderOf_dvd_of_pow_eq_one ha)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd3 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ dvd_rfl) hnot3

private theorem exists_mul_of_mem_sup_of_comm {G : Type} [Group G] {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  let S : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, h * k = x}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
        calc (h₁ * h₂) * (k₁ * k₂) = h₁ * (h₂ * k₁) * k₂ := by group
          _ = h₁ * (k₁ * h₂) * k₂ := by rw [hcomm h₂ hh₂ k₁ hk₁]
          _ = (h₁ * k₁) * (h₂ * k₂) := by group
      inv_mem' := by
        rintro a ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        rw [mul_inv_rev, hcomm h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk)] }
  have hH : H ≤ S := fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩
  have hK : K ≤ S := fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩
  exact sup_le hH hK hx

private theorem shape_of_cen {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J O₁ : Subgroup G}
    (hJ : JData n L z J)
    (hO₁le_L : O₁ ≤ Subgroup.centralizer (L : Set G))
    (hO₁dec : ∀ x ∈ Subgroup.centralizer ({b} : Set G),
      ∃ i : ℕ, ∃ o ∈ O₁, ∃ l ∈ L, x = b ^ i * o * l)
    {x : G} (hxb : x ∈ Subgroup.centralizer ({b} : Set G))
    (hx₁ : x * zs0 z = zs0 z * x) :
    ∃ i k : ℕ, ∃ o ∈ O₁, ∃ y ∈ J, x = b ^ i * zs0 z ^ k * o * y := by
  classical
  obtain ⟨i, o, hoO, l, hlL, hxeq⟩ := hO₁dec x hxb
  have hb₁L : zs0 z ∈ L := GGFF.SettingCore.zs_mem z 0
  have ho₁ : Commute o (zs0 z) :=
    (Subgroup.mem_centralizer_iff.mp (hO₁le_L hoO) _ hb₁L).symm
  have hbb₁ : Commute b (zs0 z) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le hb₁L)).symm
  have hl₁ : Commute l (zs0 z) := by
    have hA : l = (b ^ i * o)⁻¹ * x := by rw [hxeq]; group
    rw [hA]
    exact (((hbb₁.pow_left i).mul_left ho₁).inv_left).mul_left hx₁
  have hl_cen : l ∈ L ⊓ Subgroup.centralizer ({zs0 z} : Set G) :=
    ⟨hlL, Subgroup.mem_centralizer_singleton_iff.mpr hl₁.eq⟩
  rw [hJ.cen] at hl_cen
  have hcommHK : ∀ h ∈ Subgroup.zpowers (zs0 z), ∀ k ∈ J, h * k = k * h := by
    intro h hh k hk
    exact ((commute_of_mem_zpowers (hJ.comm k hk) hh).eq).symm
  obtain ⟨y0, hy0, y, hy, hy0y⟩ := exists_mul_of_mem_sup_of_comm hcommHK hl_cen
  obtain ⟨k, -, hk⟩ :=
    Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf (x := zs0 z) (y := y0)).mp hy0)
  refine ⟨i, k, o, hoO, y, hy, ?_⟩
  rw [hxeq, ← hy0y, ← hk]
  have ho1k : o * (zs0 z ^ k * y) = zs0 z ^ k * (o * y) := by
    rw [← mul_assoc, (ho₁.pow_right k).eq, mul_assoc]
  rw [show b ^ i * o * (zs0 z ^ k * y) = b ^ i * (o * (zs0 z ^ k * y)) by group, ho1k]
  group

private theorem shape_of_cen_of_comm_J {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J O₁ : Subgroup G}
    (hJ : JData n L z J)
    (hO₁le_L : O₁ ≤ Subgroup.centralizer (L : Set G))
    (hO₁dec : ∀ x ∈ Subgroup.centralizer ({b} : Set G),
      ∃ i : ℕ, ∃ o ∈ O₁, ∃ l ∈ L, x = b ^ i * o * l)
    {x : G} (hxb : x ∈ Subgroup.centralizer ({b} : Set G))
    (hx₁ : x * zs0 z = zs0 z * x)
    (hxJ : ∀ y ∈ J, x * y = y * x) :
    ∃ i k : ℕ, ∃ o ∈ O₁, x = b ^ i * zs0 z ^ k * o := by
  obtain ⟨i, k, o, hoO, y, hy, hxeq⟩ := shape_of_cen h hJ hO₁le_L hO₁dec hxb hx₁
  have hy1 : y = 1 := by
    refine center_J h hJ y hy ?_
    intro z' hz'
    have hbz : Commute b z' :=
      (Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le (hJ.le hz'))).symm
    have hb₁z : Commute (zs0 z) z' := (hJ.comm z' hz').symm
    have hoz : Commute o z' :=
      (Subgroup.mem_centralizer_iff.mp (hO₁le_L hoO) z' (hJ.le hz')).symm
    have hAz : Commute (b ^ i * zs0 z ^ k * o) z' :=
      ((hbz.pow_left i).mul_left (hb₁z.pow_left k)).mul_left hoz
    have hxy : (b ^ i * zs0 z ^ k * o) * y = x := by rw [hxeq]
    have hyz : y * z' = z' * y := by
      refine mul_left_cancel (a := b ^ i * zs0 z ^ k * o) ?_
      calc (b ^ i * zs0 z ^ k * o) * (y * z')
          = ((b ^ i * zs0 z ^ k * o) * y) * z' := by group
        _ = x * z' := by rw [hxy]
        _ = z' * x := hxJ z' hz'
        _ = z' * ((b ^ i * zs0 z ^ k * o) * y) := by rw [hxy]
        _ = (z' * (b ^ i * zs0 z ^ k * o)) * y := by group
        _ = ((b ^ i * zs0 z ^ k * o) * z') * y := by rw [← hAz.eq]
        _ = (b ^ i * zs0 z ^ k * o) * (z' * y) := by group
    exact hyz
  rw [hy1, mul_one] at hxeq
  exact ⟨i, k, o, hoO, hxeq⟩

private theorem r_normalizes_O₁ {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J B₂ A R : Subgroup G}
    (hJ : JData n L z J) (hR : RData b z J B₂ A R) {O₁ : Subgroup G}
    (hO₁le_b : O₁ ≤ Subgroup.centralizer ({b} : Set G))
    (hO₁le_L : O₁ ≤ Subgroup.centralizer (L : Set G))
    (hO₁dec : ∀ x ∈ Subgroup.centralizer ({b} : Set G),
      ∃ i : ℕ, ∃ o ∈ O₁, ∃ l ∈ L, x = b ^ i * o * l)
    (hnot3 : ¬ 3 ∣ Nat.card O₁) :
    ∀ o ∈ O₁, ∀ r ∈ R, r * o * r⁻¹ ∈ O₁ := by
  classical
  intro o hoO r hr
  have hRcomm : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := by
    have hh := (isMulCommutative_iff.mp hR.b2.abel.1 : ∀ a b : ↥B₂, a * b = b * a)
    intro r hr s hs
    exact congrArg Subtype.val (hh ⟨r, hR.le hr⟩ ⟨s, hR.le hs⟩)
  have hb₁L : zs0 z ∈ L := GGFF.SettingCore.zs_mem z 0
  have hb₁R : zs0 z ∈ R := hR.b₁_mem
  set o' : G := r * o * r⁻¹ with ho'def
  have ho'b₁ : Commute o' (zs0 z) := by
    have hr' : Commute r (zs0 z) := hRcomm r hr _ hb₁R
    have ho' : Commute o (zs0 z) :=
      (Subgroup.mem_centralizer_iff.mp (hO₁le_L hoO) _ hb₁L).symm
    have h := (hr'.mul_left ho').mul_left hr'.inv_left
    simpa [ho'def] using h
  have ho'J : ∀ z' ∈ J, o' * z' = z' * o' := by
    intro z' hz'
    have hrz : Commute r z' := hR.cenJ r hr z' hz'
    have hoz : Commute o z' :=
      (Subgroup.mem_centralizer_iff.mp (hO₁le_L hoO) z' (hJ.le hz')).symm
    have h := (hrz.mul_left hoz).mul_left hrz.inv_left
    simpa [ho'def] using h.eq
  have ho'b : Commute o' b := by
    have hφ : b * r * b⁻¹ * r⁻¹ ∈ Subgroup.zpowers (zs0 z) := hR.comm r hr
    have hφo' : Commute (b * r * b⁻¹ * r⁻¹) o' :=
      (commute_of_mem_zpowers ho'b₁ hφ).symm
    have hmain : b * o' * b⁻¹ = o' := by
      have hob : b * o * b⁻¹ = o := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp (hO₁le_b hoO)
        rw [← h]; group
      have hconj : b * o' * b⁻¹ = (b * r * b⁻¹) * o * (b * r * b⁻¹)⁻¹ := by
        rw [ho'def]
        rw [show b * (r * o * r⁻¹) * b⁻¹
            = (b * r * b⁻¹) * (b * o * b⁻¹) * (b * r * b⁻¹)⁻¹ by group]
        rw [hob]
      have hφr : b * r * b⁻¹ = (b * r * b⁻¹ * r⁻¹) * r := by group
      rw [hconj, hφr]
      have hmid : (b * r * b⁻¹ * r⁻¹) * r * o * ((b * r * b⁻¹ * r⁻¹) * r)⁻¹
          = (b * r * b⁻¹ * r⁻¹) * o' * (b * r * b⁻¹ * r⁻¹)⁻¹ := by
        rw [ho'def]; group
      rw [hmid, hφo'.eq]
      group
    show o' * b = b * o'
    calc o' * b = (b * o' * b⁻¹) * b := by rw [hmain]
      _ = b * o' := by group
  have hxb : o' ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun z' hz' => by
      rw [Set.mem_singleton_iff] at hz'
      subst hz'
      exact ho'b.eq.symm
  have hx₁ : o' * zs0 z = zs0 z * o' := ho'b₁.eq
  obtain ⟨i, k, o'', ho''O, hshape⟩ :=
    shape_of_cen_of_comm_J h hJ hO₁le_L hO₁dec hxb hx₁ ho'J
  have hshape' : o' = (b ^ i * zs0 z ^ k) * o'' := by rw [hshape]
  have hbb₁ : Commute b (zs0 z) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le hb₁L)).symm
  have hu3 : (b ^ i * zs0 z ^ k) ^ 3 = 1 := by
    rw [(hbb₁.pow_pow i k).mul_pow 3]
    rw [show (b ^ i) ^ 3 = 1 from by
          rw [← pow_mul, mul_comm, pow_mul, h.settingCore.b_cube, one_pow],
        show (zs0 z ^ k) ^ 3 = 1 from by
          rw [← pow_mul, mul_comm, pow_mul, h.settingCore.zs_pow 0, one_pow],
        mul_one]
  have hu_dvd3 : orderOf (b ^ i * zs0 z ^ k) ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
  have ho''b : Commute o'' b :=
    Subgroup.mem_centralizer_singleton_iff.mp (hO₁le_b ho''O)
  have ho''b₁ : Commute o'' (zs0 z) :=
    (Subgroup.mem_centralizer_iff.mp (hO₁le_L ho''O) _ hb₁L).symm
  have hcomm_u_o'' : Commute o'' (b ^ i * zs0 z ^ k) :=
    (ho''b.pow_right i).mul_right (ho''b₁.pow_right k)
  have hu_dvd_lcm : orderOf (b ^ i * zs0 z ^ k) ∣ Nat.lcm (orderOf o'') (orderOf o') := by
    have h := hcomm_u_o''.orderOf_dvd_lcm_mul
    rwa [show o'' * (b ^ i * zs0 z ^ k) = o' from by rw [hshape', hcomm_u_o''.eq]] at h
  have hnot3_o' : ¬ 3 ∣ orderOf o' := by
    have hord : orderOf o' = orderOf o := by
      rw [ho'def]
      exact (SemiconjBy.orderOf_eq r (x := o) (y := r * o * r⁻¹)
        (by unfold SemiconjBy; group)).symm
    rw [hord]
    exact fun h3 => hnot3 (h3.trans (Subgroup.orderOf_dvd_natCard O₁ hoO))
  have hnot3_o'' : ¬ 3 ∣ orderOf o'' :=
    fun h3 => hnot3 (h3.trans (Subgroup.orderOf_dvd_natCard O₁ ho''O))
  have hlcm_not3 : ¬ 3 ∣ Nat.lcm (orderOf o'') (orderOf o') :=
    (show Nat.Prime 3 from by norm_num).not_dvd_lcm hnot3_o'' hnot3_o'
  have hnot3_u : ¬ 3 ∣ orderOf (b ^ i * zs0 z ^ k) :=
    fun h3 => hlcm_not3 (h3.trans hu_dvd_lcm)
  have hu_eq_one : orderOf (b ^ i * zs0 z ^ k) = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hu_dvd3 with hh | hh
    · exact hh
    · exact absurd (hh ▸ dvd_rfl) hnot3_u
  have hu1 : b ^ i * zs0 z ^ k = 1 := orderOf_eq_one_iff.mp hu_eq_one
  rw [hshape', hu1, one_mul]
  exact ho''O

theorem cen_b_decomp {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J B₂ A R : Subgroup G}
    (hJ : JData n L z J) (hR : RData b z J B₂ A R) :
    ∃ O : Subgroup G,
      O ≤ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (R : Set G) ∧
      O ≤ Subgroup.centralizer (L : Set G) ∧ ¬ 3 ∣ Nat.card O ∧
      ∀ x ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (R : Set G),
        ∃ i : ℕ, ∃ o ∈ O, ∃ y ∈ J, x = GGFF.zs z 0 ^ i * o * y := by
  classical
  obtain ⟨O₁, hO₁le_b, hO₁le_L, _, hO₁not3, hO₁dec⟩ := exists_cen_decomp h (odd_cen h)
  have hb₁L : zs0 z ∈ L := GGFF.SettingCore.zs_mem z 0
  have hb₁R : zs0 z ∈ R := hR.b₁_mem
  have hinf : Subgroup.zpowers (zs0 z) ⊓ O₁ = ⊥ :=
    inf_zpowers_eq_bot_of_not_dvd (h.settingCore.zs_pow 0) hO₁not3
  have hOnorm : ∀ o ∈ O₁, ∀ r ∈ R, r * o * r⁻¹ ∈ O₁ :=
    r_normalizes_O₁ h hJ hR hO₁le_b hO₁le_L hO₁dec hO₁not3
  have hRcomm : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := by
    have hh := (isMulCommutative_iff.mp hR.b2.abel.1 : ∀ a b : ↥B₂, a * b = b * a)
    intro r hr s hs
    exact congrArg Subtype.val (hh ⟨r, hR.le hr⟩ ⟨s, hR.le hs⟩)
  refine ⟨O₁ ⊓ Subgroup.centralizer (R : Set G), ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    exact ⟨hO₁le_b hx.1, hx.2⟩
  · intro x hx
    exact hO₁le_L (Subgroup.mem_inf.mp hx).1
  · intro h3
    exact hO₁not3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxb, hxR⟩ := hx
    have hx₁ : x * zs0 z = zs0 z * x :=
      (Subgroup.mem_centralizer_iff.mp hxR _ hb₁R).symm
    obtain ⟨i, k, o, hoO, y, hy, hxshape⟩ :=
      shape_of_cen h hJ hO₁le_L hO₁dec hxb hx₁
    have hkey : ∀ r ∈ R, (o * r = r * o) ∧ (b * r * b⁻¹ * r⁻¹) ^ i = 1 := by
      intro r hr
      have hbb₁ : Commute b (zs0 z) :=
        (Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le hb₁L)).symm
      set φ : G := b * r * b⁻¹ * r⁻¹ with hφdef
      set C : G := o * r * o⁻¹ * r⁻¹ with hCdef
      have hφmem : φ ∈ Subgroup.zpowers (zs0 z) := by rw [hφdef]; exact hR.comm r hr
      have hbφ : Commute b φ := commute_of_mem_zpowers hbb₁ hφmem
      have hbr : b * r * b⁻¹ = φ * r := by rw [hφdef]; group
      have hpow := pow_conj_eq_phi_pow_mul hbφ hbr i
      have hCmem : C ∈ O₁ := by
        rw [hCdef]
        have h2 : r * o⁻¹ * r⁻¹ ∈ O₁ := hOnorm o⁻¹ (O₁.inv_mem hoO) r hr
        simpa only [mul_assoc] using O₁.mul_mem hoO h2
      have hCb : Commute C b :=
        Subgroup.mem_centralizer_singleton_iff.mp (hO₁le_b hCmem)
      have hcb : Commute C (b ^ i) := hCb.pow_right i
      have hb₁comm : Commute (zs0 z ^ k) (o * r * o⁻¹) := by
        have ho' : Commute o (zs0 z) :=
          (Subgroup.mem_centralizer_iff.mp (hO₁le_L hoO) _ hb₁L).symm
        have hr' : Commute r (zs0 z) := hRcomm r hr _ hb₁R
        exact ((ho'.mul_left hr').mul_left ho'.inv_left).symm.pow_left k
      have hinner : (zs0 z ^ k * o) * r * (zs0 z ^ k * o)⁻¹ = o * r * o⁻¹ := by
        rw [show (zs0 z ^ k * o) * r * (zs0 z ^ k * o)⁻¹
            = zs0 z ^ k * (o * r * o⁻¹) * (zs0 z ^ k)⁻¹ by group]
        exact hb₁comm.mul_inv_cancel
      have hA1 : (b ^ i * zs0 z ^ k * o) * r * (b ^ i * zs0 z ^ k * o)⁻¹
          = b ^ i * (o * r * o⁻¹) * (b ^ i)⁻¹ := by
        rw [show b ^ i * zs0 z ^ k * o = b ^ i * (zs0 z ^ k * o) by group]
        rw [show (b ^ i * (zs0 z ^ k * o)) * r * (b ^ i * (zs0 z ^ k * o))⁻¹
            = b ^ i * ((zs0 z ^ k * o) * r * (zs0 z ^ k * o)⁻¹) * (b ^ i)⁻¹ by group]
        rw [hinner]
      have hor : o * r * o⁻¹ = C * r := by rw [hCdef]; group
      have hAconj : (b ^ i * zs0 z ^ k * o) * r * (b ^ i * zs0 z ^ k * o)⁻¹
          = C * φ ^ i * r := by
        rw [hA1, hor]
        calc b ^ i * (C * r) * (b ^ i)⁻¹
            = (b ^ i * C) * r * (b ^ i)⁻¹ := by group
          _ = (C * b ^ i) * r * (b ^ i)⁻¹ := by rw [← hcb.eq]
          _ = C * (b ^ i * r * (b ^ i)⁻¹) := by group
          _ = C * (φ ^ i * r) := by rw [hpow]
          _ = C * φ ^ i * r := by group
      have hAy : x = (b ^ i * zs0 z ^ k * o) * y := by rw [hxshape]
      have hyr : y * r * y⁻¹ = r := by
        have hc : Commute y r := (hR.cenJ r hr y hy).symm
        exact hc.mul_inv_cancel
      have hxconj : x * r * x⁻¹ = C * φ ^ i * r := by
        rw [hAy]
        rw [show ((b ^ i * zs0 z ^ k * o) * y) * r * ((b ^ i * zs0 z ^ k * o) * y)⁻¹
            = (b ^ i * zs0 z ^ k * o) * (y * r * y⁻¹) * (b ^ i * zs0 z ^ k * o)⁻¹ by group]
        rw [hyr, hAconj]
      have hxr : x * r * x⁻¹ = r := by
        have hc : Commute x r := (Subgroup.mem_centralizer_iff.mp hxR r hr).symm
        exact hc.mul_inv_cancel
      have hCphi : C * φ ^ i = 1 := by
        have h1 : C * φ ^ i * r = r := by rw [← hxconj, hxr]
        calc C * φ ^ i = (C * φ ^ i * r) * r⁻¹ := by group
          _ = r * r⁻¹ := by rw [h1]
          _ = 1 := by group
      have hCeq : C = (φ ^ i)⁻¹ := by
        calc C = C * φ ^ i * (φ ^ i)⁻¹ := by group
          _ = 1 * (φ ^ i)⁻¹ := by rw [hCphi]
          _ = (φ ^ i)⁻¹ := by rw [one_mul]
      have hC1 : C = 1 := by
        have hφpow : φ ^ i ∈ Subgroup.zpowers (zs0 z) := by
          obtain ⟨m, -, hm⟩ := Finset.mem_image.mp
            ((mem_zpowers_iff_mem_range_orderOf (x := zs0 z) (y := φ)).mp hφmem)
          rw [← hm, ← pow_mul]
          exact Subgroup.npow_mem_zpowers (zs0 z) (m * i)
        have hmem : C ∈ Subgroup.zpowers (zs0 z) ⊓ O₁ :=
          ⟨hCeq ▸ Subgroup.inv_mem _ hφpow, hCmem⟩
        rw [hinf] at hmem
        exact Subgroup.mem_bot.mp hmem
      have hφi : φ ^ i = 1 := by
        rw [hC1, one_mul] at hCphi
        exact hCphi
      have ho_comm : o * r = r * o := by
        have hCr : o * r * o⁻¹ * r⁻¹ = 1 := hCdef ▸ hC1
        calc o * r = (o * r * o⁻¹ * r⁻¹) * (r * o) := by group
          _ = 1 * (r * o) := by rw [hCr]
          _ = r * o := by rw [one_mul]
      have hφi' : (b * r * b⁻¹ * r⁻¹) ^ i = 1 := by rw [← hφdef]; exact hφi
      exact ⟨ho_comm, hφi'⟩
    obtain ⟨r₀, hr₀R, hr₀ne⟩ := hR.nonc
    have ho_cenR : o ∈ Subgroup.centralizer (R : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun r hr => (hkey r hr).1.symm
    have hφ₀i : (b * r₀ * b⁻¹ * r₀⁻¹) ^ i = 1 := (hkey r₀ hr₀R).2
    have hφ₀mem : b * r₀ * b⁻¹ * r₀⁻¹ ∈ Subgroup.zpowers (zs0 z) := hR.comm r₀ hr₀R
    have hφ₀3 : (b * r₀ * b⁻¹ * r₀⁻¹) ^ 3 = 1 := by
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp
        ((mem_zpowers_iff_mem_range_orderOf (x := zs0 z)
          (y := b * r₀ * b⁻¹ * r₀⁻¹)).mp hφ₀mem)
      rw [← hm, ← pow_mul, mul_comm, pow_mul, h.settingCore.zs_pow 0, one_pow]
    have hφ₀ord : orderOf (b * r₀ * b⁻¹ * r₀⁻¹) = 3 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp
        (orderOf_dvd_of_pow_eq_one hφ₀3) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hr₀ne
      · exact h
    have h3dvd : 3 ∣ i := by
      rw [← hφ₀ord]
      exact orderOf_dvd_of_pow_eq_one hφ₀i
    have hbi : b ^ i = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, h.hypA.ord]
      exact h3dvd
    refine ⟨k, o, ⟨hoO, ho_cenR⟩, y, hy, ?_⟩
    rw [hxshape, hbi, one_mul]

end CFSG.StandardType.FF81.PropOne

end
