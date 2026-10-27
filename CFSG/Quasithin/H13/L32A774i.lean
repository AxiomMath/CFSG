module

public import CFSG.Quasithin.H13.L32A72c
public import CFSG.Quasithin.H13.L32A774d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem prime_dvd_relIndex {P D : Subgroup G} (hDP : D ≤ Subgroup.normalizer (P : Set G))
    {p : ℕ} (hp : p.Prime) {g : G} (hgD : g ∈ D) (hgP : g ∉ P) (hgp : g ^ p ∈ P) :
    p ∣ P.relIndex D := by
  have : Fact p.Prime := ⟨hp⟩
  have : (P.subgroupOf D).Normal := ⟨fun n hn d => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hDP d.2) n).mp hn⟩
  have hx1 : (QuotientGroup.mk (⟨g, hgD⟩ : ↥D) : ↥D ⧸ P.subgroupOf D) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hgP
  have hxp : (QuotientGroup.mk (⟨g, hgD⟩ : ↥D) : ↥D ⧸ P.subgroupOf D) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact hgp
  show p ∣ Nat.card (↥D ⧸ P.subgroupOf D)
  rw [← orderOf_eq_prime hxp hx1]
  exact orderOf_dvd_natCard _

theorem eq_one_or_seven {i j : ℕ} (hij : j * i = 168) (h3 : 3 ∣ j) (h2 : 2 ∣ j) (h8 : i ≤ 8)
    (h4 : i ≤ 4 → i = 1) : i = 1 ∨ i = 7 := by
  rcases Nat.lt_or_ge 4 i with h | h
  · interval_cases i <;> omega
  · exact Or.inl (h4 h)

theorem exists_fix_of_ncard (L : Subgroup G) {Ω : Set G} (hΩ : Ω.ncard = 8)
    (hΩL : ∀ l ∈ L, ∀ w ∈ Ω, l * w * l⁻¹ ∈ Ω) {c₀ : G} (hc₀ : c₀ ∈ Ω)
    (h17 : ((Subgroup.centralizer ({c₀} : Set G)).subgroupOf L).index = 1 ∨
      ((Subgroup.centralizer ({c₀} : Set G)).subgroupOf L).index = 7) :
    ∃ w ∈ Ω, ∀ l ∈ L, l * w * l⁻¹ = w := by
  rcases h17 with h1 | h7
  · refine ⟨c₀, hc₀, fun l hl => ?_⟩
    have hl' : (⟨l, hl⟩ : ↥L) ∈ (Subgroup.centralizer ({c₀} : Set G)).subgroupOf L := by
      rw [Subgroup.index_eq_one.mp h1]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hl'
    rw [show l * c₀ = c₀ * l from hl', mul_inv_cancel_right]
  · have hOc : {x | ∃ l ∈ L, l * c₀ * l⁻¹ = x}.ncard = 7 := by
      rw [ncard_conj_eq_index, h7]
    obtain ⟨w, hwΩ, hwO⟩ : ∃ w ∈ Ω, w ∉ {x | ∃ l ∈ L, l * c₀ * l⁻¹ = x} := by
      by_contra h
      push Not at h
      have := Set.ncard_le_ncard (s := Ω) (t := {x | ∃ l ∈ L, l * c₀ * l⁻¹ = x}) h
      omega
    refine ⟨w, hwΩ, fun l hl => ?_⟩
    by_contra hne
    have hlw : l * w * l⁻¹ ∉ {x | ∃ l ∈ L, l * c₀ * l⁻¹ = x} := by
      rintro ⟨m, hm, hmw⟩
      apply hwO
      refine ⟨l⁻¹ * m, mul_mem (inv_mem hl) hm, ?_⟩
      rw [show l⁻¹ * m * c₀ * (l⁻¹ * m)⁻¹ = l⁻¹ * (m * c₀ * m⁻¹) * l by group, hmw]
      group
    have hsub : {x | ∃ l ∈ L, l * c₀ * l⁻¹ = x} ∪ {w, l * w * l⁻¹} ⊆ Ω := by
      rintro x (⟨m, hm, rfl⟩ | rfl | rfl)
      · exact hΩL m hm c₀ hc₀
      · exact hwΩ
      · exact hΩL l hl w hwΩ
    have hdisj : Disjoint {x | ∃ l ∈ L, l * c₀ * l⁻¹ = x} ({w, l * w * l⁻¹} : Set G) := by
      rw [Set.disjoint_left]
      rintro x hx (rfl | rfl)
      · exact hwO hx
      · exact hlw hx
    have h2 : ({w, l * w * l⁻¹} : Set G).ncard = 2 := Set.ncard_pair (Ne.symm hne)
    have := Set.ncard_le_ncard hsub
    rw [Set.ncard_union_eq hdisj, hOc, h2, hΩ] at this
    omega

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem relIndex_pCoreOf : (pCoreOf 2 L).relIndex L = 168 := by
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have h1281 := C.hyp.hyp1281One C.h13322 C.hMod
  obtain ⟨hcard, hsq, -⟩ := h1281.card_sq
  have : IsMulCommutative ↥V := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).1.1
  obtain ⟨e⟩ : Nonempty (↥V ≃* Multiplicative (Fin 3 → ZMod 2)) :=
    Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one
      (fun x => Subtype.ext (by simpa using hsq x x.2)) hcard
  have hs := repV_surjective hLV e (autOn_eq_top_of_hyp1281One h1281)
  have hk : (repV hLV e).ker = (pCoreOf 2 L).subgroupOf L := by
    rw [repV_ker, C.pCoreOf_eq]
    ext l
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨l.2, h⟩, fun h => h.2⟩
  have hcard168 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [Matrix.card_SL_field]
    simp [Fin.prod_univ_three]
  rw [Subgroup.relIndex, ← hk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs,
    Subgroup.card_top, hcard168]

theorem exists_x3_transv : ∃ x y : G, x ∈ L₁Of L (fsuV1 T V) ∧ x ^ 3 = 1 ∧
    x ∉ pCoreOf 2 L ∧ y ∈ L₁Of L (fsuV1 T V) ∧ y ∉ pCoreOf 2 L ∧ y ^ 2 ∈ pCoreOf 2 L := by
  obtain ⟨V₂, hV2⟩ := C.hyp.exists_V2 C.h13322 C.hMod C.h1222
  have : IsMulCommutative ↥V := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).1.1
  have S14 := C.hyp.set14 C.h1222 C.h1332 C.h1334 hV2
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    F7.isElemAbelian_comm hUe (v_le_fsuU ha) (v_le_fsuU hb)
  have hV2' : ∀ a ∈ V, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one hUe (v_le_fsuU ha)
  obtain ⟨z, a, b, hz0, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis
  have hzV₂ : z ∈ V₂ := hV2.1 hz0
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
  have haV' : a ∈ V := hV2.2.1 ha
  obtain ⟨x₁, hx₁L, hx₁3, hx₁z, hx₁a, hx₁b⟩ := S14.exists_rot hzV haV' hb
    (fun h => haV (h ▸ one_mem _)) (fun h => hbV (h ▸ one_mem _))
    (fun h => haV (h ▸ hz0)) (fun h => hbV (h ▸ hzV₂)) (fun h => hbV (h ▸ ha))
    (fun h => hbV (h ▸ mul_mem hzV₂ ha))
  obtain ⟨x₂, hx₂L, hx₂3, hx₂z, hx₂a, hx₂b⟩ := S14.exists_rot hzV haV' (mul_mem hzV hb)
    (fun h => haV (h ▸ one_mem _))
    (fun h => hbV (by
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_mem hzV₂))
    (fun h => haV (h ▸ hz0))
    (fun h => hbV (by
      have : b = 1 := by
        calc b = z⁻¹ * (z * b) := by group
          _ = 1 := by rw [h, inv_mul_cancel]
      rw [this]
      exact one_mem _))
    (fun h => hbV (by
      have : b = z⁻¹ * a := by
        calc b = z⁻¹ * (z * b) := by group
          _ = z⁻¹ * a := by rw [← h]
      rw [this]
      exact mul_mem (inv_mem hzV₂) ha))
    (fun h => hbV (by
      have : b = a := by
        calc b = z⁻¹ * (z * b) := by group
          _ = z⁻¹ * (z * a) := by rw [h]
          _ = a := by group
      rw [this]
      exact ha))
  have hx₁L1 : x₁ ∈ L₁Of L (fsuV1 T V) :=
    Subgroup.subset_closure ⟨⟨hx₁L, S14.mem_g1 hz0 hz1 hx₁z⟩, 3, by decide, hx₁3⟩
  have hx₂L1 : x₂ ∈ L₁Of L (fsuV1 T V) :=
    Subgroup.subset_closure ⟨⟨hx₂L, S14.mem_g1 hz0 hz1 hx₂z⟩, 3, by decide, hx₂3⟩
  have hnot : ∀ g w, w ∈ V → g * w * g⁻¹ ≠ w → g ∉ pCoreOf 2 L := fun g w hw hne hg => hne (by
    rw [C.pCoreOf_eq] at hg
    rw [(Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).2 w hw).symm,
      mul_inv_cancel_right])
  have hx₁z' : x₁⁻¹ * z * x₁ = z := by
    calc x₁⁻¹ * z * x₁ = x₁⁻¹ * (x₁ * z * x₁⁻¹) * x₁ := by rw [hx₁z]
      _ = z := by group
  have hx₁b' : x₁⁻¹ * b * x₁ = a := by
    calc x₁⁻¹ * b * x₁ = x₁⁻¹ * (x₁ * a * x₁⁻¹) * x₁ := by rw [hx₁a]
      _ = a := by group
  have hx₁ab' : x₁⁻¹ * (a * b) * x₁ = b := by
    calc x₁⁻¹ * (a * b) * x₁ = x₁⁻¹ * (x₁ * b * x₁⁻¹) * x₁ := by rw [hx₁b]
      _ = b := by group
  have hx₂b' : x₂ * b * x₂⁻¹ = a * b := by
    calc x₂ * b * x₂⁻¹ = (x₂ * z * x₂⁻¹)⁻¹ * (x₂ * (z * b) * x₂⁻¹) := by group
      _ = z⁻¹ * (a * (z * b)) := by rw [hx₂z, hx₂b]
      _ = a * b := by
          rw [inv_eq_of_mul_eq_one_right (hV2' z hzV),
            show z * (a * (z * b)) = (z * a) * (z * b) by group, hVc z hzV a haV',
            show a * z * (z * b) = a * (z * z) * b by group, hV2' z hzV, mul_one]
  obtain ⟨y, hy⟩ : ∃ y, y = x₁⁻¹ * x₂ := ⟨_, rfl⟩
  have hyL1 : y ∈ L₁Of L (fsuV1 T V) := by
    rw [hy]
    exact mul_mem (inv_mem hx₁L1) hx₂L1
  have hya : y * a * y⁻¹ = z * a := by
    calc y * a * y⁻¹ = x₁⁻¹ * (x₂ * a * x₂⁻¹) * x₁ := by rw [hy]; group
      _ = x₁⁻¹ * (z * b) * x₁ := by rw [hx₂a]
      _ = (x₁⁻¹ * z * x₁) * (x₁⁻¹ * b * x₁) := by group
      _ = z * a := by rw [hx₁z', hx₁b']
  have hyz : y * z * y⁻¹ = z := by
    calc y * z * y⁻¹ = x₁⁻¹ * (x₂ * z * x₂⁻¹) * x₁ := by rw [hy]; group
      _ = z := by rw [hx₂z, hx₁z']
  have hyb : y * b * y⁻¹ = b := by
    calc y * b * y⁻¹ = x₁⁻¹ * (x₂ * b * x₂⁻¹) * x₁ := by rw [hy]; group
      _ = b := by rw [hx₂b', hx₁ab']
  refine ⟨x₁, y, hx₁L1, hx₁3, hnot x₁ a haV' (by rw [hx₁a]; exact fun h => hbV (h ▸ ha)),
    hyL1, hnot y a haV' (by
      rw [hya]
      intro h
      apply hz1
      calc z = z * a * a⁻¹ := by group
        _ = 1 := by rw [h, mul_inv_cancel]), ?_⟩
  have hyL : y ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hyL1
  have h2z : (y * y) * z * (y * y)⁻¹ = z := by
    rw [show (y * y) * z * (y * y)⁻¹ = y * (y * z * y⁻¹) * y⁻¹ by group, hyz, hyz]
  have h2a : (y * y) * a * (y * y)⁻¹ = a := by
    rw [show (y * y) * a * (y * y)⁻¹ = y * (y * a * y⁻¹) * y⁻¹ by group, hya,
      show y * (z * a) * y⁻¹ = (y * z * y⁻¹) * (y * a * y⁻¹) by group, hyz, hya,
      ← mul_assoc, hV2' z hzV, one_mul]
  have h2b : (y * y) * b * (y * y)⁻¹ = b := by
    rw [show (y * y) * b * (y * y)⁻¹ = y * (y * b * y⁻¹) * y⁻¹ by group, hyb, hyb]
  have hy2 : y ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
    rw [pow_two, Subgroup.mem_centralizer_iff]
    intro v hv
    have h := conj_eq_of_basis S14 hz0 hz1 ha haV hb hbV h2z h2a h2b hv
    calc v * (y * y) = (y * y) * v * (y * y)⁻¹ * (y * y) := by rw [h]
      _ = (y * y) * v := by group
  rw [C.pCoreOf_eq]
  exact Subgroup.mem_inf.mpr ⟨pow_mem hyL 2, hy2⟩

theorem eq_of_relIndex_le_four {D : Subgroup G} (hDL : D ≤ L) (h4 : D.relIndex L ≤ 4) :
    D = L := by
  have h24 : (D.subgroupOf L).normalCore.index ≤ 24 :=
    (Subgroup.index_normalCore_le_factorial_index (D.subgroupOf L)).trans
      ((Nat.factorial_le h4).trans (by decide))
  by_cases hx : ∃ x ∈ (D.subgroupOf L).normalCore, (x : G) ∉ Subgroup.centralizer (V : Set G)
  · obtain ⟨x, hxN, hxV⟩ := hx
    have hconj : ∀ l ∈ L, ∀ n ∈ (D.subgroupOf L).normalCore.map L.subtype,
        l * n * l⁻¹ ∈ (D.subgroupOf L).normalCore.map L.subtype := by
      rintro l hl _ ⟨n, hn, rfl⟩
      exact ⟨⟨l, hl⟩ * n * ⟨l, hl⟩⁻¹,
        (Subgroup.normalCore_normal (D.subgroupOf L)).conj_mem n hn _, rfl⟩
    have hNL := normal_eq_of_not_mem_centralizer C.hyp C.h13322 C.hMod C.h1222 C.h1332 C.h1334
      (Subgroup.map_subtype_le _) hconj (Subgroup.mem_map_of_mem L.subtype hxN) hxV
    refine le_antisymm hDL fun l hl => ?_
    rw [← hNL] at hl
    obtain ⟨n, hn, rfl⟩ := hl
    exact Subgroup.mem_subgroupOf.mp (Subgroup.normalCore_le _ hn)
  · push Not at hx
    have hle : (D.subgroupOf L).normalCore ≤ (pCoreOf 2 L).subgroupOf L := fun x hx' => by
      rw [Subgroup.mem_subgroupOf, C.pCoreOf_eq]
      exact Subgroup.mem_inf.mpr ⟨x.2, hx x hx'⟩
    have h168 := Subgroup.index_dvd_of_le hle
    rw [show ((pCoreOf 2 L).subgroupOf L).index = 168 from C.relIndex_pCoreOf] at h168
    have hpos : (D.subgroupOf L).normalCore.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) h168
    omega

theorem mem_fsuV1_of_conj_mem {w : G} (hw : ∀ k ∈ kz T V, k * w * k⁻¹ ∈ V) :
    w ∈ fsuV1 T V := by
  have hKH : kz T V ≤ hz T V := oTwoUpper_le _
  let D : Subgroup G :=
    { carrier := {x | ∀ k ∈ kz T V, k * x * k⁻¹ ∈ V}
      one_mem' := fun k _ => by simp
      mul_mem' := fun {x y} hx hy k hk => by
        rw [show k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) by group]
        exact mul_mem (hx k hk) (hy k hk)
      inv_mem' := fun {x} hx k hk => by
        rw [show k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ by group]
        exact inv_mem (hx k hk) }
  have hDV : D ≤ V := fun x hx => by
    have := hx 1 (one_mem _)
    simpa using this
  have hV1D : fsuV1 T V ≤ D := fun x hx k hk => by
    rw [(Subgroup.mem_centralizer_iff.mp (hKH hk) x hx).symm, mul_inv_cancel_right]
    exact (Subgroup.mem_inf.mp hx).1
  have hDK : kz T V ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_of_conj_mem' fun k₀ hk₀ x hx k hk => by
      rw [show k * (k₀ * x * k₀⁻¹) * k⁻¹ = (k * k₀) * x * (k * k₀)⁻¹ by group]
      exact hx _ (mul_mem hk hk₀)
  by_contra hwV1
  have hne : D ≠ fsuV1 T V := fun h => hwV1 (by
    rw [← h]
    exact hw)
  have hDU := C.eq_fsuU_of hV1D (hDV.trans fun x hx => v_le_fsuU hx) hDK hne
  obtain ⟨u, hu, huV⟩ := C.exists_mem_fsuU C.u0_eq
  exact huV (hDV (by rw [hDU]; exact hu))

theorem kz_comm_of {w : G} (hw : ∀ k ∈ kz T V, k * w * k⁻¹ * w⁻¹ ∈ fsuV1 T V) :
    ∀ k ∈ kz T V, k * w = w * k := by
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hle : kz T V ≤ Subgroup.centralizer ({w} : Set G) := by
    refine (Subgroup.closure_le _).mpr fun g hg => ?_
    obtain ⟨hgH, hodd⟩ := hg
    have hgK : g ∈ kz T V := Subgroup.subset_closure ⟨hgH, hodd⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨v, hv⟩ : ∃ v, v = g * w * g⁻¹ * w⁻¹ := ⟨_, rfl⟩
    have hvV1 : v ∈ fsuV1 T V := by
      rw [hv]
      exact hw g hgK
    have hgv : g * v = v * g := (Subgroup.mem_centralizer_iff.mp hgH v hvV1).symm
    have hv2 : v * v = 1 := by
      rw [← pow_two]
      exact F7.isElemAbelian_pow_eq_one hUe (v_le_fsuU (Subgroup.mem_inf.mp hvV1).1)
    have e1 : g * w = v * w * g := by rw [hv]; group
    have hg2 : (g * g) * w = w * (g * g) := by
      calc (g * g) * w = g * (g * w) := by group
        _ = g * (v * w * g) := by rw [e1]
        _ = (g * v) * w * g := by group
        _ = (v * g) * w * g := by rw [hgv]
        _ = v * (g * w) * g := by group
        _ = v * (v * w * g) * g := by rw [e1]
        _ = (v * v) * w * (g * g) := by group
        _ = w * (g * g) := by rw [hv2, one_mul]
    obtain ⟨m, hm⟩ := hodd
    have hgm : (g * g) ^ (m + 1) = g := by
      rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf g + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    have hc := ((show Commute (g * g) w from hg2).pow_left (m + 1)).eq
    rwa [hgm] at hc
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk)

end Ctx73

end CFSG.Quasithin.H13.L32A
