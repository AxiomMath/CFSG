module

public import CFSG.Quasithin.Recognition.HSType129d
public import CFSG.Quasithin.Recognition.HSTypeS5Rec
public import CFSG.Quasithin.Recognition.HSType129b
public import CFSG.Quasithin.Recognition.HSType129c
public import CFSG.Quasithin.Recognition.HSTypeL12h

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.GorensteinWalter

abbrev cenX {G : Type*} [Group G] (x : G) : Subgroup ↥(Subgroup.centralizer ({x} : Set G)) :=
  (Subgroup.zpowers x).subgroupOf (Subgroup.centralizer ({x} : Set G))

theorem mem_cenX {G : Type*} [Group G] {x : G} {c : ↥(Subgroup.centralizer ({x} : Set G))} :
    c ∈ cenX x ↔ (c : G) ∈ Subgroup.zpowers x :=
  Subgroup.mem_subgroupOf

instance cenX_normal {G : Type*} [Group G] (x : G) : (cenX x).Normal where
  conj_mem n hn c := by
    rw [mem_cenX] at hn ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute (c : G) x := Subgroup.mem_centralizer_singleton_iff.mp c.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hk, (hc.zpow_right k).eq,
      mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers x k

abbrev cenQuot {G : Type*} [Group G] (x : G) : Type _ :=
  ↥(Subgroup.centralizer ({x} : Set G)) ⧸ cenX x

theorem cenQuot_mk_eq_one_iff {G : Type*} [Group G] {x : G}
    (c : ↥(Subgroup.centralizer ({x} : Set G))) :
    (QuotientGroup.mk c : cenQuot x) = 1 ↔ (c : G) ∈ Subgroup.zpowers x := by
  rw [QuotientGroup.eq_one_iff, mem_cenX]

theorem eq_of_mk_eq_of_mul_self {G : Type*} [Group G] {x : G} (hx3 : orderOf x = 3)
    {a b : ↥(Subgroup.centralizer ({x} : Set G))} (ha : (a : G) * a = 1) (hb : (b : G) * b = 1)
    (hab : (QuotientGroup.mk a : cenQuot x) = QuotientGroup.mk b) : a = b := by
  rw [QuotientGroup.eq, mem_cenX] at hab
  have hy : (a : G)⁻¹ * b ∈ Subgroup.zpowers x := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at hab
    exact hab
  have hya : (a : G) * ((a : G)⁻¹ * b) = ((a : G)⁻¹ * b) * a := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hk]
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp a.2) k).eq
  have hy2 : ((a : G)⁻¹ * b) ^ 2 = 1 := by
    have e : (b : G) * b = (a * a) * (((a : G)⁻¹ * b) * ((a : G)⁻¹ * b)) := by
      calc (b : G) * b = (a * ((a : G)⁻¹ * b)) * (a * ((a : G)⁻¹ * b)) := by group
        _ = a * (((a : G)⁻¹ * b) * a) * ((a : G)⁻¹ * b) := by group
        _ = a * (a * ((a : G)⁻¹ * b)) * ((a : G)⁻¹ * b) := by rw [← hya]
        _ = (a * a) * (((a : G)⁻¹ * b) * ((a : G)⁻¹ * b)) := by group
    rw [hb, ha, one_mul] at e
    rw [sq]
    exact e.symm
  have h3 : orderOf ((a : G)⁻¹ * b) ∣ 3 := hx3 ▸ orderOf_dvd_of_mem_zpowers hy
  have h2 : orderOf ((a : G)⁻¹ * b) ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
  have h1 : orderOf ((a : G)⁻¹ * b) = 1 := by
    have := Nat.dvd_gcd h3 h2
    rw [show Nat.gcd 3 2 = 1 by norm_num] at this
    exact Nat.dvd_one.mp this
  rw [orderOf_eq_one_iff] at h1
  apply Subtype.ext
  calc (a : G) = a * ((a : G)⁻¹ * b) := by rw [h1, mul_one]
    _ = b := by group

namespace HSSetting

theorem cenQuot_s4_or_s5
    {G : Type} [Group G] [Finite G] {z : G} {V : Subgroup G} (h : HSSetting z V) {x : G}
    (hxH : x ∈ hsH z) (hx3 : orderOf x = 3) {w : G} (hwx : w * x = x * w) (hw3 : orderOf w = 3)
    (hwX : w ∉ Subgroup.zpowers x) :
    Nonempty (cenQuot x ≃* Equiv.Perm (Fin 4)) ∨ Nonempty (cenQuot x ≃* Equiv.Perm (Fin 5)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({x} : Set G) with hC
  set q : ↥C →* cenQuot x := QuotientGroup.mk' (cenX x) with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hq1 : ∀ c : ↥C, q c = 1 ↔ (c : G) ∈ Subgroup.zpowers x := fun c =>
    cenQuot_mk_eq_one_iff c
  have hdet : ∀ a b : ↥C, (a : G) * a = 1 → (b : G) * b = 1 → q a = q b → a = b :=
    fun a b ha hb hab => eq_of_mk_eq_of_mul_self hx3 ha hb hab
  obtain ⟨d, hdH, hdK, hd2, hdx⟩ := h.exists_invol_centralizer_three hxH hx3
  set D := hsD z d with hD
  have hDle : D ≤ hsH z ⊓ C := h.hsD_le hxH hx3 hdH hdx
  have hDC : D ≤ C := hDle.trans inf_le_right
  set DC := D.subgroupOf C with hDCdef
  have hcardDC : Nat.card DC = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv, h.card_hsD hdH hdK hd2]
  have hDCp : IsPGroup 2 DC := IsPGroup.of_card (n := 3) (by rw [hcardDC]; norm_num)
  obtain ⟨S, hS⟩ := hDCp.exists_le_sylow
  have hSeq : (S : Subgroup ↥C) = DC := by
    have hP := h.eq_hsD_of_le hxH hx3 hdH hdK hd2 hdx (P := (S : Subgroup ↥C).map C.subtype)
      (S.isPGroup'.map _) (fun y hy => ⟨⟨y, hDC hy⟩, hS (Subgroup.mem_subgroupOf.mpr hy), rfl⟩)
      (Subgroup.map_subtype_le _)
    ext c
    constructor
    · intro hc
      have hc' : (c : G) ∈ (S : Subgroup ↥C).map C.subtype := ⟨c, hc, rfl⟩
      rw [hP] at hc'
      exact Subgroup.mem_subgroupOf.mpr hc'
    · intro hc
      exact hS hc
  set Dbar : Sylow 2 (cenQuot x) := S.mapSurjective hqs with hDbar
  have hDbar' : (Dbar : Subgroup (cenQuot x)) = DC.map q := by
    rw [hDbar, Sylow.coe_mapSurjective, hSeq]
  obtain ⟨u, huZ, hu1, huz, huu⟩ := h.exists_mem_ZQ_ne
  have hwz : u ∉ Subgroup.zpowers z := by
    intro hwz
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hwz with h1 | h1
    · exact hu1 h1
    · exact huz h1
  have huD : u ∈ D := Subgroup.mem_sup_left huZ
  have hdD : d ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have hou : orderOf u = 4 := by
    have h1 : ¬ u ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq, huu]
      exact h.z_ne_one
    have h2 : u ^ 2 ^ (1 + 1) = 1 := by
      rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, sq u, huu, sq, h.z_mul_z]
    exact (orderOf_eq_prime_pow h1 h2).trans (by norm_num)
  have hDiso : Nonempty (↥D ≃* DihedralGroup 4) := by
    set ρ : ↥D := ⟨u, huD⟩ with hρ
    set σ : ↥D := ⟨d, hdD⟩ with hσ
    have hgen : (⊤ : Subgroup ↥D) = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
      refine le_antisymm (fun y _ => ?_) le_top
      have hmap : (Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ).map D.subtype =
          Subgroup.zpowers u ⊔ Subgroup.zpowers d := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        rfl
      have hy : (y : G) ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers d := by
        have hyD : (y : G) ∈ hsZQ z ⊔ Subgroup.zpowers d := y.2
        rw [← h.zpowers_eq_ZQ huZ hwz] at hyD
        exact hyD
      rw [← hmap] at hy
      obtain ⟨y', hy', hyy⟩ := hy
      exact (Subtype.ext hyy : y' = y) ▸ hy'
    have hσ2 : σ ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact hd2)
    have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (h.inv_of_not_mem_K hdH hdK huZ)
    have hσρ : σ ∉ Subgroup.zpowers ρ := by
      intro hσρ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hσρ
      have hdu : d = u ^ k := by
        have := congrArg Subtype.val hk
        rw [Subgroup.coe_zpow] at this
        exact this.symm
      apply hdK
      rw [hdu]
      exact (hsK z).zpow_mem (h.Q_le_K huZ.1) k
    have := dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
    rwa [hρ, Subgroup.orderOf_mk, hou] at this
  have hXD : Subgroup.zpowers x ⊓ D = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard
    (by rw [Nat.card_zpowers, hx3, h.card_hsD hdH hdK hd2]; norm_num))
  have hinj : Function.Injective (q.domRestrict DC) := by
    refine (injective_iff_map_eq_one _).mpr fun a ha => ?_
    have ha' : ((a : ↥C) : G) ∈ Subgroup.zpowers x ⊓ D :=
      ⟨(hq1 a).mp ha, Subgroup.mem_subgroupOf.mp a.2⟩
    rw [hXD, Subgroup.mem_bot] at ha'
    exact Subtype.ext (Subtype.ext ha')
  have hrange : (q.domRestrict DC).range = (Dbar : Subgroup (cenQuot x)) := by
    rw [MonoidHom.domRestrict_range, hDbar']
  have eD : (Dbar : Subgroup (cenQuot x)) ≃* DihedralGroup 4 :=
    (MulEquiv.subgroupCongr hrange).symm.trans ((MonoidHom.ofInjective hinj).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hDC).trans hDiso.some))
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp hxH).symm
  obtain ⟨zc, hzc⟩ : ∃ zc : ↥C, (zc : G) = z := ⟨⟨z, hzC⟩, rfl⟩
  have hzz : (zc : G) * zc = 1 := by rw [hzc]; exact h.z_mul_z
  have hz1 : z ∉ Subgroup.zpowers x := by
    intro hz
    have hz' : z ∈ Subgroup.zpowers x ⊓ D := ⟨hz, Subgroup.mem_sup_left h.z_mem_ZQ⟩
    rw [hXD, Subgroup.mem_bot] at hz'
    exact h.z_ne_one hz'
  have hoz : orderOf (q zc) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hz1 (hzc ▸ (hq1 zc).mp h1)
    rw [← map_pow, sq, show zc * zc = 1 from Subtype.ext hzz, map_one]
  have hxD : x ∈ Subgroup.normalizer (D : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · have hc : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp (hDC hy)
      rw [← hc, mul_inv_cancel_right]
      exact hy
    · have hc := Subgroup.mem_centralizer_singleton_iff.mp (hDC hy)
      have e : y = x * y * x⁻¹ := by
        calc y = x⁻¹ * ((x * y * x⁻¹) * x) := by group
          _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [hc]
          _ = x * y * x⁻¹ := by group
      rw [e]
      exact hy
  have hXDeq : Subgroup.zpowers x ⊔ D = hsH z ⊓ C := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le ?_ hDle) ?_
    · exact (Subgroup.zpowers_le).mpr ⟨hxH, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    · rw [h.card_centralizer_H_three hxH hx3]
      have hXN : Subgroup.zpowers x ≤ Subgroup.normalizer (D : Set G) :=
        (Subgroup.zpowers_le).mpr hxD
      have := card_sup_mul_card_inf_of_le_normalizer hXN
      rw [hXD, Subgroup.card_bot, mul_one, Nat.card_zpowers, hx3, h.card_hsD hdH hdK hd2] at this
      omega
  have hcen : Subgroup.centralizer ({q zc} : Set (cenQuot x)) = (Dbar : Subgroup (cenQuot x)) := by
    rw [hDbar']
    apply le_antisymm
    · intro yb hyb
      obtain ⟨c, rfl⟩ := hqs yb
      have hcz : q c * q zc = q zc * q c := Subgroup.mem_centralizer_singleton_iff.mp hyb
      have hc1 : c * zc * c⁻¹ = zc := by
        refine hdet _ _ ?_ hzz (by rw [map_mul, map_mul, map_inv, hcz, mul_inv_cancel_right])
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          show (c : G) * zc * (c : G)⁻¹ * ((c : G) * zc * (c : G)⁻¹) =
            c * ((zc : G) * zc) * (c : G)⁻¹ by group, hzz, mul_one, mul_inv_cancel]
      have hcz' : (c : G) * z = z * c := by
        have e := congrArg Subtype.val hc1
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hzc] at e
        calc (c : G) * z = (c : G) * z * (c : G)⁻¹ * c := by group
          _ = z * c := by rw [e]
      have hcHC : (c : G) ∈ hsH z ⊓ C :=
        ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcz', c.2⟩
      rw [← hXDeq] at hcHC
      obtain ⟨k, δ, hδ, hcδ⟩ := mem_sup_zpowers hxD hcHC
      have hxkC : x ^ k ∈ C := C.zpow_mem (Subgroup.mem_centralizer_singleton_iff.mpr rfl) k
      have hceq : c = ⟨x ^ k, hxkC⟩ * ⟨δ, hDC hδ⟩ := Subtype.ext hcδ
      refine ⟨⟨δ, hDC hδ⟩, Subgroup.mem_subgroupOf.mpr hδ, ?_⟩
      rw [hceq, map_mul, (hq1 ⟨x ^ k, hxkC⟩).mpr (Subgroup.zpow_mem_zpowers x k), one_mul]
    · rintro _ ⟨δ, hδ, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have hδH : ((δ : ↥C) : G) ∈ hsH z := (hDle (Subgroup.mem_subgroupOf.mp hδ)).1
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hzc]
      exact Subgroup.mem_centralizer_singleton_iff.mp hδH
  obtain ⟨g, hg⟩ := h.exists_conj_of_invol hdH hdK hd2 huZ hwz h.z_mul_z h.z_ne_one
  obtain ⟨e₀, f₀, he₀D, hf₀D, he₀2, hf₀2, he₀K, hf₀K, ⟨g₁, hg₁⟩, hf₀z⟩ :
      ∃ e₀ f₀ : G, e₀ ∈ D ∧ f₀ ∈ D ∧ e₀ * e₀ = 1 ∧ f₀ * f₀ = 1 ∧ e₀ ∉ hsK z ∧ f₀ ∉ hsK z ∧
        (∃ g : G, g * z * g⁻¹ = e₀) ∧ ∀ g : G, g * z * g⁻¹ ≠ f₀ := by
    have hduD : d * u ∈ D := D.mul_mem hdD huD
    have hdu2 : d * u * (d * u) = 1 := by
      have hinv := h.inv_of_not_mem_K hdH hdK huZ
      calc d * u * (d * u) = (d * u * d⁻¹) * (d * d) * u := by group
        _ = 1 := by rw [hinv, hd2, mul_one, inv_mul_cancel]
    have hduK : d * u ∉ hsK z := fun hK => hdK (by
      have := (hsK z).mul_mem hK ((hsK z).inv_mem (h.Q_le_K huZ.1))
      rwa [mul_inv_cancel_right] at this)
    rcases hg with hg | hg
    · exact ⟨d, d * u, hdD, hduD, hd2, hdu2, hdK, hduK, ⟨g, hg⟩,
        (h.not_conj_mul_of_conj_z hdH hdK hd2 huZ hwz hg).1⟩
    · have hwZ' : u⁻¹ ∈ hsZQ z := (hsZQ z).inv_mem huZ
      have hwz' : u⁻¹ ∉ Subgroup.zpowers z := fun h' => hwz (by
        have := (Subgroup.zpowers z).inv_mem h'
        rwa [inv_inv] at this)
      have hduH : d * u ∈ hsH z := (hsH z).mul_mem hdH (h.Q_le_H huZ.1)
      have hnc := (h.not_conj_mul_of_conj_z hduH hduK hdu2 hwZ' hwz' hg).1
      simp only [mul_inv_cancel_right] at hnc
      exact ⟨d * u, d, hduD, hdD, hdu2, hd2, hduK, hdK, ⟨g, hg⟩, hnc⟩
  set ec : ↥C := ⟨e₀, hDC he₀D⟩ with hec
  set fc : ↥C := ⟨f₀, hDC hf₀D⟩ with hfc
  have h1C : ((1 : ↥C) : G) * (1 : ↥C) = 1 := by rw [Subgroup.coe_one, one_mul]
  have hoe : orderOf (q ec) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← map_pow, sq, show ec * ec = 1 from Subtype.ext he₀2, map_one]
    · have := hdet ec 1 he₀2 h1C (by rw [h1, map_one])
      apply he₀K
      rw [show e₀ = ((ec : ↥C) : G) from rfl, this]
      exact (hsK z).one_mem
  have hof : orderOf (q fc) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← map_pow, sq, show fc * fc = 1 from Subtype.ext hf₀2, map_one]
    · have := hdet fc 1 hf₀2 h1C (by rw [h1, map_one])
      apply hf₀K
      rw [show f₀ = ((fc : ↥C) : G) from rfl, this]
      exact (hsK z).one_mem
  have heD : q ec ∈ (Dbar : Subgroup (cenQuot x)) := by
    rw [hDbar']
    exact ⟨ec, Subgroup.mem_subgroupOf.mpr he₀D, rfl⟩
  have hfD : q fc ∈ (Dbar : Subgroup (cenQuot x)) := by
    rw [hDbar']
    exact ⟨fc, Subgroup.mem_subgroupOf.mpr hf₀D, rfl⟩
  have hez : q ec ≠ q zc := by
    intro he
    have := hdet ec zc he₀2 hzz he
    apply he₀K
    rw [show e₀ = ((ec : ↥C) : G) from rfl, this, hzc]
    exact h.Q_le_K h.mem_Q
  have hze : IsConj (q zc) (q ec) := by
    have hex : e₀ * x = x * e₀ := Subgroup.mem_centralizer_singleton_iff.mp (hDC he₀D)
    obtain ⟨c, hcx, hcz⟩ := h.exists_centralizer_conj hxH hx3 hex hg₁
    have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hcx
    refine isConj_iff.mpr ⟨q ⟨c, hcC⟩, ?_⟩
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hzc]
    exact hcz
  have hzf : ¬ IsConj (q zc) (q fc) := by
    intro hc
    obtain ⟨cb, hcb⟩ := isConj_iff.mp hc
    obtain ⟨c, rfl⟩ := hqs cb
    have hsq : ((c * zc * c⁻¹ : ↥C) : G) * ((c * zc * c⁻¹ : ↥C) : G) = 1 := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        show (c : G) * zc * (c : G)⁻¹ * ((c : G) * zc * (c : G)⁻¹) =
          c * ((zc : G) * zc) * (c : G)⁻¹ by group, hzz, mul_one, mul_inv_cancel]
    have := hdet (c * zc * c⁻¹) fc hsq hf₀2 (by rw [map_mul, map_mul, map_inv, hcb])
    apply hf₀z c
    have e := congrArg Subtype.val this
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hzc] at e
    exact e
  have hwC : w ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hwx
  have how : orderOf (q ⟨w, hwC⟩) = 3 := by
    refine orderOf_eq_prime ?_ fun h1 => hwX ((hq1 _).mp h1)
    rw [← map_pow]
    have e : (⟨w, hwC⟩ : ↥C) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← hw3, pow_orderOf_eq_one]
      rfl)
    rw [e, map_one]
  exact s4_or_s5_of_dihedral Dbar eD hoz hcen hoe heD hez hze hof hfD hzf how

end HSSetting

end CFSG.Quasithin.HSType
