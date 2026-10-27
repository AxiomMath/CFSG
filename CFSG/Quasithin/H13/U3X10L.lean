module

public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.Background.C1PackS15212A
public import CFSG.Quasithin.H13.L32NModule
public import CFSG.Quasithin.H13.L32NSet14Act
public import CFSG.Quasithin.H13.U3C137

public section

namespace CFSG.Quasithin.H13

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise IsMulCommutative

variable {G : Type} [Group G]

namespace L32NSet14.Setting

variable [Finite G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V] (S : Setting G T L V V₂)
include S

theorem exists_conj_eq {z u w : G} (hz : z ∈ fsuV1 T V) (hu : u ∈ V)
    (hw : w ∈ V) (hu1 : u ≠ 1) (huz : u ≠ z) (hw1 : w ≠ 1) (hwz : w ≠ z) :
    ∃ g ∈ L, g * z * g⁻¹ = z ∧ g * u * g⁻¹ = w := by
  have hzV : z ∈ V := (mem_inf.mp hz).1
  have hrot : ∀ {u w : G}, u ∈ V → w ∈ V → u ≠ 1 → u ≠ z → w ≠ 1 → w ≠ z → u ≠ w →
      w ≠ z * u → ∃ g ∈ L, g * z * g⁻¹ = z ∧ g * u * g⁻¹ = w := by
    intro u w hu hw hu1 huz hw1 hwz huw hwzu
    obtain ⟨l, hl, -, hlz, hlu, -⟩ := S.exists_rot hzV hu hw hu1 hw1 huz hwz huw hwzu
    exact ⟨l, hl, hlz, hlu⟩
  by_cases huw : u = w
  · exact ⟨1, one_mem _, by group, by rw [huw]; group⟩
  by_cases hwzu : w = z * u
  ·
    obtain ⟨-, a, b, -, -, ha, haV, hb, hbV⟩ := S.exists_basis
    have hzV₂ : z ∈ V₂ := S.hV2.1 hz
    have hzu : z * u ∈ V := mul_mem hzV hu
    obtain ⟨v, hv, hv1, hvz, hvu, hvzu⟩ : ∃ v ∈ V, v ≠ 1 ∧ v ≠ z ∧ v ≠ u ∧ v ≠ z * u := by
      by_cases hu2 : u ∈ V₂
      · exact ⟨b, hb, fun h => hbV (h ▸ one_mem _), fun h => hbV (h ▸ hzV₂),
          fun h => hbV (h ▸ hu2), fun h => hbV (h ▸ mul_mem hzV₂ hu2)⟩
      · have haV' : a ∈ V := S.hV2.2.1 ha
        refine ⟨a, haV', fun h => haV (h ▸ one_mem _), fun h => haV (h ▸ hz),
          fun h => hu2 (h ▸ ha), fun h => hu2 ?_⟩
        have : u = z * a := by
          rw [h, ← mul_assoc, S.mul_self_V hzV, one_mul]
        rw [this]
        exact mul_mem hzV₂ ha
    obtain ⟨g₁, hg₁, hg₁z, hg₁u⟩ := hrot hu hv hu1 huz hv1 hvz (fun h => hvu h.symm) hvzu
    have hzuz : z * u ≠ z := fun h => hu1 (by
      have := congrArg (fun t => z⁻¹ * t) h
      simpa using this)
    have hzu1 : z * u ≠ 1 := fun h => huz (by
      have := congrArg (fun t => z * t) h
      rwa [← mul_assoc, S.mul_self_V hzV, one_mul, mul_one] at this)
    have hzv : z * u ≠ z * v := fun h => hvu (by
      have := congrArg (fun t => z⁻¹ * t) h
      simpa using this.symm)
    obtain ⟨g₂, hg₂, hg₂z, hg₂v⟩ := hrot hv hzu hv1 hvz hzu1 hzuz (fun h => hvzu h) hzv
    refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_, ?_⟩
    · calc g₂ * g₁ * z * (g₂ * g₁)⁻¹ = g₂ * (g₁ * z * g₁⁻¹) * g₂⁻¹ := by group
        _ = z := by rw [hg₁z, hg₂z]
    · calc g₂ * g₁ * u * (g₂ * g₁)⁻¹ = g₂ * (g₁ * u * g₁⁻¹) * g₂⁻¹ := by group
        _ = w := by rw [hg₁u, hg₂v, hwzu]
  · exact hrot hu hw hu1 huz hw1 hwz huw hwzu

theorem isSylowTwoOf_inf : IsSylowTwoOf (T ⊓ L) L := by
  have hloc := S.hH.faithful.1
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, hloc.1, hloc.2.2.1⟩
  exact A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer S.TL)

theorem L₁T_eq {z : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) :
    L₁Of L (fsuV1 T V) ⊔ T = (L ⊔ T) ⊓ centralizer ({z} : Set G) := by
  have hTz : T ≤ centralizer ({z} : Set G) := fun t ht => by
    have hZ : quasithinOmegaOneCenter T ≤ T ⊓ centralizer (T : Set G) :=
      (closure_le _).mpr fun _ hz => hz.1
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.mp (hZ (mem_inf.mp hz).2).2 t ht)
  apply le_antisymm
  · refine le_inf (sup_le_sup_right (L1_le.trans inf_le_left) T) (sup_le ?_ hTz)
    intro g hg
    have hgN := (L1_le hg).2
    exact mem_centralizer_singleton_iff.2 (by
      have := le_centralizer_normalizer_of_card_eq_two S.card_V1 hz
      exact (mem_centralizer_iff.1 this) g hgN)
  · rintro g ⟨hgX, hgz⟩
    obtain ⟨l, hl, t, ht, rfl⟩ : ∃ l ∈ L, ∃ t ∈ T, g = l * t := by
      have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
        coe_mul_of_right_le_normalizer_left L T S.TL
      have hx' : g ∈ (L : Set G) * (T : Set G) := by
        rw [← hmul]
        exact hgX
      obtain ⟨l, hl, t', ht', rfl⟩ := Set.mem_mul.mp hx'
      exact ⟨l, hl, t', ht', rfl⟩
    have hlz : l * z * l⁻¹ = z := by
      have h1 := mem_centralizer_singleton_iff.1 hgz
      have h2 := mem_centralizer_singleton_iff.1 (hTz ht)
      calc l * z * l⁻¹ = (l * t) * z * (l * t)⁻¹ := by
            rw [show (l * t) * z * (l * t)⁻¹ = l * (t * z * t⁻¹) * l⁻¹ by group]
            rw [show t * z * t⁻¹ = z by rw [h2, mul_inv_cancel_right]]
        _ = z := by rw [h1, mul_inv_cancel_right]
    have hlN : l ∈ L ⊓ normalizer (fsuV1 T V : Set G) := ⟨hl, S.mem_g1 hz hz1 hlz⟩
    have hTN : T ⊓ L ≤ L ⊓ normalizer (fsuV1 T V : Set G) := fun t ht => ⟨ht.2, S.T_V1 ht.1⟩
    have hsyl : IsSylowTwoOf (T ⊓ L) (L ⊓ normalizer (fsuV1 T V : Set G)) :=
      C1GN.isSylowTwoOf_of_le S.isSylowTwoOf_inf hTN inf_le_left
    have h := C1Pack12.oTwoUpper_sup_eq_of_sylow hsyl
    have hl' : l ∈ L₁Of L (fsuV1 T V) ⊔ T := by
      rw [← h, ← oTwoRes_eq_oTwoUpper] at hlN
      have h' : oTwoRes (L ⊓ normalizer (fsuV1 T V : Set G)) ⊔ (T ⊓ L) ≤
          L₁Of L (fsuV1 T V) ⊔ T := sup_le_sup_left inf_le_left _
      exact h' hlN
    exact mul_mem hl' (mem_sup_right ht)

theorem L₁T_max {z : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (H : Subgroup G)
    (hPH : L₁Of L (fsuV1 T V) ⊔ T ≤ H) (hHX : H ≤ L ⊔ T) :
    H = L₁Of L (fsuV1 T V) ⊔ T ∨ H = L ⊔ T := by
  by_cases hHz : H ≤ centralizer ({z} : Set G)
  · left
    exact le_antisymm (by rw [S.L₁T_eq hz hz1]; exact le_inf hHX hHz) hPH
  right
  obtain ⟨h, hhH, hhz⟩ := IsConcreteLE.not_le_iff_exists.1 hHz
  have hzV : z ∈ V := (mem_inf.mp hz).1
  have hXV : L ⊔ T ≤ normalizer (V : Set G) := sup_le S.LV S.TV
  have hhN := hXV (hHX hhH)
  have hw : h * z * h⁻¹ ∈ V := (mem_normalizer_iff.1 hhN z).1 hzV
  have hw1 : h * z * h⁻¹ ≠ 1 := fun h' => hz1 (by
    calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
      _ = 1 := by rw [h']; group)
  have hwz : h * z * h⁻¹ ≠ z := fun h' => hhz (mem_centralizer_singleton_iff.2 (by
    calc h * z = h * z * h⁻¹ * h := by group
      _ = z * h := by rw [h']))
  have hP : L₁Of L (fsuV1 T V) ⊔ T = (L ⊔ T) ⊓ centralizer ({z} : Set G) := S.L₁T_eq hz hz1
  refine le_antisymm hHX (sup_le (fun l hl => ?_) (le_sup_right.trans hPH))
  have hv : l * z * l⁻¹ ∈ V := (mem_normalizer_iff.1 (S.LV hl) z).1 hzV
  obtain ⟨k, hkH, hkz⟩ : ∃ k ∈ H, k * z * k⁻¹ = l * z * l⁻¹ := by
    by_cases hvz : l * z * l⁻¹ = z
    · exact ⟨1, one_mem _, by rw [hvz]; group⟩
    have hv1 : l * z * l⁻¹ ≠ 1 := fun h' => hz1 (by
      calc z = l⁻¹ * (l * z * l⁻¹) * l := by group
        _ = 1 := by rw [h']; group)
    obtain ⟨g, hgL, hgz, hgw⟩ := S.exists_conj_eq hz hw hv hw1 hwz hv1 hvz
    have hgH : g ∈ H := hPH (by
      rw [hP]
      exact ⟨mem_sup_left hgL, mem_centralizer_singleton_iff.2 (by
        calc g * z = g * z * g⁻¹ * g := by group
          _ = z * g := by rw [hgz])⟩)
    refine ⟨g * h, mul_mem hgH hhH, ?_⟩
    calc g * h * z * (g * h)⁻¹ = g * (h * z * h⁻¹) * g⁻¹ := by group
      _ = l * z * l⁻¹ := hgw
  have hkl : k⁻¹ * l ∈ L₁Of L (fsuV1 T V) ⊔ T := by
    rw [hP]
    refine mem_inf.2 ⟨mul_mem (inv_mem (hHX hkH)) (mem_sup_left hl),
      mem_centralizer_singleton_iff.2 ?_⟩
    calc k⁻¹ * l * z = k⁻¹ * (l * z * l⁻¹) * l := by group
      _ = k⁻¹ * (k * z * k⁻¹) * l := by rw [hkz]
      _ = z * (k⁻¹ * l) := by group
  have := mul_mem hkH (hPH hkl)
  rwa [mul_inv_cancel_left] at this

end L32NSet14.Setting

namespace U3

theorem card_autOn_dvd [Finite G] {L V : Subgroup G} (hLV : L ≤ normalizer (V : Set G))
    (hO : pCoreOf 2 L ≤ centralizer (V : Set G)) :
    Nat.card ↥(autOn L V) ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hO2 : CFSG.pCore 2 ↥L ≤ (A6.autOnHom hLV).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxC : (x : G) ∈ centralizer (V : Set G) := hO (coe_mem_pCoreOf_iff.2 hx)
    exact Subtype.ext (by
      rw [A6.autOnHom_apply]
      exact A1b.conjAct_eq_one_iff.2 hxC)
  let φ₁ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(autOn L V) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) (A6.autOnHom hLV) hO2
  have hφ₁ : Function.Surjective φ₁ := by
    intro y
    obtain ⟨x, rfl⟩ := A6.autOnHom_surjective hLV y
    exact ⟨(x : ↥L ⧸ CFSG.pCore 2 ↥L), rfl⟩
  exact Subgroup.card_dvd_of_surjective hφ₁

theorem stmt13_3_10_L32 (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2) (h1334 : A6.Stmt13_3_4)
    (hC137 : C137Statement) [Finite G] {T L V : Subgroup G} (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) (hZV : V ⊓ centralizer (L : Set G) = ⊥)
    (hlin : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) :
    CharNormal (baum (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))) (L ⊔ T) ∨ IsLnBlock L 3 := by
  have hcL : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
    obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hlin
    rw [Nat.card_congr e.toEquiv, HSType.card_SL_three_two]
  obtain ⟨-, ⟨hTL, -, -, -⟩, ⟨-, hall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, -, -, hab, hmod⟩ := hall V hV
  have hLV : L ≤ normalizer (V : Set G) := hV.2.2.1
  have hO : pCoreOf 2 L ≤ centralizer (V : Set G) := by
    refine (pCoreOf_le_pCoreOf_sup hTL).trans ?_
    intro k hk
    exact mem_centralizer_iff.2 fun v hv => ((mem_reducedAggregate' (hV.1 hv)).2.1 k hk).symm
  have hdvd := card_autOn_dvd hLV hO
  rw [hcL] at hdvd
  obtain ⟨hab', hnat⟩ :
      ∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 3 1 := by
    rcases hmod with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨-, hc2, -⟩ | ⟨-, hn, -⟩ | ⟨hu, -, -⟩
    · exfalso
      obtain ⟨e⟩ := A6.nonempty_mulEquiv_of_realizes (A6.altDn_faithful (by norm_num)) h5
      have e' : ↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5)) := e
      rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin] at hdvd
      norm_num [Nat.factorial] at hdvd
    · exfalso
      obtain ⟨e⟩ := A6.nonempty_mulEquiv_of_realizes (A6.altDn_faithful (by norm_num)) h6
      have e' : ↥(autOn L V) ≃* ↥(alternatingGroup (Fin 6)) := e
      rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin] at hdvd
      norm_num [Nat.factorial] at hdvd
    · exfalso
      rw [hZV, card_bot] at hc2
      exact absurd hc2 (by norm_num)
    · exact ⟨hab, hn⟩
    · exfalso
      have := card_of_lieModel_PSU_three_three hu
      omega
  have h1281 := L32NSet14.hyp1281One h1332 hH hV hlin hnat
  have hV1 := L32NSet14.isTSub_V1 h1332 h1334 hH hV hZV
  obtain ⟨V₂, hV₂, h12⟩ := exists_v2_of_hyp1281One h1222 h1281 hV1
  have hV2 : A6.IsV2 T V V₂ := ⟨h12, hV₂.1, hV₂.2.2, by rw [hV₂.2.1]; norm_num⟩
  let S : L32NSet14.Setting G T L V V₂ := ⟨h1222, h1332, h1334, hH, hV, hZV, hV2, hlin, hnat⟩
  obtain ⟨z, -, -, hz, hz1, -, -, -, -⟩ := S.exists_basis
  have hcharL : CharTwo L := A5.charTwo_of_faithful hH.qtke.2.1 hH.sylow hH.faithful
  have hLT : ∀ x ∈ L ⊔ T, ∃ l ∈ L, ∃ t ∈ T, x = l * t := by
    intro x hx
    have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
      coe_mul_of_right_le_normalizer_left L T hTL
    have hx' : x ∈ (L : Set G) * (T : Set G) := by
      rw [← hmul]
      exact hx
    obtain ⟨l, hl, t', ht', rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨l, hl, t', ht', rfl⟩
  have hVL : ⁅V, L⁆ = V := hV.2.2.2.1
  have htop : autOn L V = ⊤ := autOn_eq_top_of_hyp1281One h1281
  have hlt : L₁Of L (fsuV1 T V) ⊔ T < L ⊔ T := by
    refine lt_of_le_of_ne (sup_le_sup_right (L32NSet14.Setting.L1_le.trans inf_le_left) T)
      fun h => ?_
    have hLz : L ≤ centralizer ({z} : Set G) :=
      (le_sup_left.trans h.symm.le).trans ((S.L₁T_eq hz hz1).le.trans inf_le_right)
    have hzC : z ∈ V ⊓ centralizer (L : Set G) :=
      ⟨(mem_inf.mp hz).1, mem_centralizer_iff.2 fun l hl => mem_centralizer_singleton_iff.1
        (hLz hl)⟩
    rw [hZV, mem_bot] at hzC
    exact hz1 hzC
  have hred : IsTwoReducedIn (L ⊔ T) V := by
    have hyp := L32NSet14.hyp1223 h1332 hH hV
    rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
    · exact absurd hAlt hyp.notAlt
    obtain ⟨-, -, hall'⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
    obtain ⟨⟨hVT', -, hred', -⟩, -, -, -⟩ := hall' V hyp.irrPlus
    exact isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVT'.trans le_sup_right, hred'⟩
  have hzV : z ∈ V := (mem_inf.mp hz).1
  rcases hC137 G (L ⊔ T) T V L (L₁Of L (fsuV1 T V) ⊔ T) (L₁Of L (fsuV1 T V) ⊔ T)
      (charTwo_sup_of_normalizes hH.sylow.1 hTL hcharL)
      (A5.isSylowTwoOf_of_le hH.sylow le_sup_right) hLT hH.faithful.1.2.1 hcharL
      (Or.inl hlin) (Or.inr (by rw [htop]; exact le_top)) le_sup_right le_rfl hlt
      (S.L₁T_max hz hz1) (Or.inl rfl) hred (by rw [hVL]; exact hV.2.1)
      (fun _ => ⟨by rw [hVL]; exact S.card_V, z, by rw [hVL]; exact hzV, hz1,
        S.L₁T_eq hz hz1⟩) with
    h | h | ⟨hc, -⟩ | h
  · exact Or.inl h
  · exact Or.inr (h.1 hlin)
  · exfalso
    have h1 : autOn (L ⊔ T) V ≤ autOn L V := by
      rw [htop]
      exact le_top
    have h2 := Subgroup.card_le_of_le h1
    rw [hc, S.card_autOn] at h2
    omega
  · exfalso
    rcases h with he | h
    · obtain ⟨e⟩ := he
      have := Nat.card_congr e.toEquiv
      rw [hcL, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at this
      norm_num [Nat.factorial] at this
    · obtain ⟨-, h3, ⟨e⟩⟩ := h
      have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
      rw [hcL, h3, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin] at h2
      norm_num [Nat.factorial] at h2

end U3

end CFSG.Quasithin.H13
