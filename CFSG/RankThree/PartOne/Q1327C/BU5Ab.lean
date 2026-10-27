module

public import CFSG.RankThree.PartOne.Q1327C.BU5Tor
public import CFSG.RankThree.PartOne.Q1327C.BU5Diag

public section

namespace CFSG.RankThree.PartOne.Q1327C

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryPlane
  CFSG.RankThree.PartOne.KFU

abbrev SU5 (f : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin 5) K) := StatedSU 5 (2 ^ f) K

abbrev ZSU5 (f : ℕ) (K : Type) [Field K] : Subgroup ↥(SU5 f K) :=
  (StatedScalars (Fin 5) K).subgroupOf (SU5 f K)

theorem exists_big_elementary {f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData 2 f K)
    (h25 : 25 ∣ 2 ^ f + 1) {Y : Type} [Group Y] (πY : ↥(SU5 f K) →* Y)
    (hker : πY.ker = ZSU5 f K) (hZMcard : Nat.card (ZSU5 f K) = 5)
    {E : Subgroup Y} (hE5 : ∀ x ∈ E, x ^ 5 = 1)
    (hab : ∀ x ∈ E.comap πY, ∀ y ∈ E.comap πY, x * y = y * x) :
    ∃ V : Subgroup Y, (∀ v ∈ V, v ^ 5 = 1) ∧ (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧
      (E.comap πY).map πY ≤ V ∧ 5 ^ 3 < Nat.card V := by
  classical
  have hfin : Finite K := hU.finite
  set Ft : Subgroup ↥(SU5 f K) := E.comap πY with hFt
  have hZM5 : ∀ z ∈ ZSU5 f K, z ^ 5 = 1 := fun z hz => by
    have := Subgroup.orderOf_dvd_natCard (ZSU5 f K) hz
    rw [hZMcard] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hxZ : ∀ x ∈ Ft, x ^ 5 ∈ ZSU5 f K := fun x hx => by
    rw [← hker, MonoidHom.mem_ker, map_pow]
    exact hE5 _ hx
  have hFt25 : ∀ x ∈ Ft, x ^ 25 = 1 := fun x hx => by
    calc x ^ 25 = (x ^ 5) ^ 5 := by rw [← pow_mul]
      _ = 1 := hZM5 _ (hxZ x hx)
  have h25K : 25 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hU.card, two_mul, pow_add]
    have h3 : 2 ^ f * 2 ^ f - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have := Nat.mul_self_sub_mul_self_eq (2 ^ f) 1
      simpa using this
    rw [h3]
    exact Dvd.dvd.mul_right h25 _
  have hrK : 5 ∣ Nat.card Kˣ := dvd_trans (by norm_num) h25K
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Kˣ, orderOf ξ = 25 := by
    have h25' : 25 ∣ Fintype.card Kˣ := by rwa [← Nat.card_eq_fintype_card]
    have hcnt := IsCyclic.card_orderOf_eq_totient (α := Kˣ) h25'
    by_contra hno
    push Not at hno
    have hempty : (Finset.univ.filter (fun a : Kˣ => orderOf a = 25)) = ∅ := by
      ext a
      simp [hno a]
    rw [hempty] at hcnt
    have : 0 < Nat.totient 25 := Nat.totient_pos.2 (by norm_num)
    simp at hcnt
    omega
  have hζ : IsPrimitiveRoot (ξ : K) 25 :=
    IsPrimitiveRoot.coe_units_iff.2 (hξ ▸ IsPrimitiveRoot.orderOf ξ)
  have hle := unitarySU_le_primeFormUnitary (n := 5) hU
  set G' : Subgroup (primeFormUnitary hU (idGram K 5)) := Ft.map (Subgroup.inclusion hle)
    with hG'
  have hG'mem : ∀ x ∈ G', ∃ x₀ ∈ Ft, Subgroup.inclusion hle x₀ = x := fun x hx => by
    obtain ⟨x₀, hx₀, hx⟩ := Subgroup.mem_map.mp hx
    exact ⟨x₀, hx₀, hx⟩
  have hGcomm : ∀ x ∈ G', ∀ y ∈ G', x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := hG'mem x hx
    obtain ⟨y₀, hy₀, rfl⟩ := hG'mem y hy
    rw [← map_mul, ← map_mul, hab x₀ hx₀ y₀ hy₀]
  have hGpow : ∀ x ∈ G', x ^ 25 = 1 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hG'mem x hx
    rw [← map_pow, hFt25 x₀ hx₀, map_one]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag_m hU hζ h25 G' hGcomm hGpow
  let ψ : ↥(SU5 f K) ≃* ↥(SU5 f K) := conjSU hU P
  have hψapp : ∀ g : ↥(SU5 f K), ((ψ g : ↥(SU5 f K)) : GL (Fin 5) K) =
      (P : GL (Fin 5) K) * g * (P : GL (Fin 5) K)⁻¹ := fun g => coe_conjSU hU P g
  have hψZ : ∀ z ∈ ZSU5 f K, ψ z = z := by
    intro z hz
    apply Subtype.ext
    rw [hψapp]
    have hzc : (z : GL (Fin 5) K) ∈ Subgroup.center (GL (Fin 5) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hz
    have hcomm := Subgroup.mem_center_iff.1 hzc (P : GL (Fin 5) K)
    calc (P : GL (Fin 5) K) * z * (P : GL (Fin 5) K)⁻¹ = (z * P) * (P : GL (Fin 5) K)⁻¹ := by
          rw [hcomm]
      _ = z := by group
  let TV : Subgroup (GL (Fin 5) K) := (torusVec25 K).map diagUHom
  have hTVle : TV ≤ SU5 f K := fun g hg =>
    torusSU_le_unitarySU hU h25 (Subgroup.map_mono torusVec25_le_torusVec hg)
  let TM : Subgroup ↥(SU5 f K) := TV.subgroupOf (SU5 f K)
  let Vt : Subgroup ↥(SU5 f K) := TM.map ψ.toMonoidHom
  have hTMd : ∀ a : ↥(SU5 f K), a ∈ TM → ∃ d : Fin 5 → Kˣ, d ∈ torusVec25 K ∧
      (a : GL (Fin 5) K) = diagU d := fun a ha => by
    obtain ⟨d, hd, hda⟩ := Subgroup.mem_subgroupOf.1 ha
    exact ⟨d, hd, hda.symm⟩
  have hTMcomm : ∀ a b : ↥(SU5 f K), a ∈ TM → b ∈ TM → a * b = b * a := by
    intro a b ha hb
    obtain ⟨d, -, hd⟩ := hTMd a ha
    obtain ⟨d', -, hd'⟩ := hTMd b hb
    apply Subtype.ext
    show (a : GL (Fin 5) K) * b = b * a
    rw [hd, hd', diagU_mul, diagU_mul, mul_comm]
  have hTM5 : ∀ a : ↥(SU5 f K), a ∈ TM → a ^ 5 ∈ ZSU5 f K := by
    intro a ha
    obtain ⟨d, hd, hda⟩ := hTMd a ha
    have h1 : ((a ^ 5 : ↥(SU5 f K)) : GL (Fin 5) K) ∈ StatedScalars (Fin 5) K := by
      rw [Subgroup.coe_pow, hda]
      exact diagU_pow_five_mem_scalars hd.2.2
    exact h1
  have hFtV : ∀ x ∈ Ft, x ∈ Vt := by
    intro x hx
    set g : ↥(SU5 f K) := ψ.symm x with hgdef
    have hgx : ψ g = x := ψ.apply_symm_apply x
    have hx_eq : (x : GL (Fin 5) K) = (P : GL (Fin 5) K) * g * (P : GL (Fin 5) K)⁻¹ := by
      rw [← hψapp g, hgx]
    have hgdiag : ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag := by
      have hx' := hP (Subgroup.inclusion hle x) ⟨x, hx, rfl⟩
      have hco : (((P⁻¹ * Subgroup.inclusion hle x * P : primeFormUnitary hU (idGram K 5)) :
          GL (Fin 5) K)) = (g : GL (Fin 5) K) := by
        show (P : GL (Fin 5) K)⁻¹ * (x : GL (Fin 5) K) * (P : GL (Fin 5) K) = g
        rw [hx_eq]
        group
      rw [hco] at hx'
      exact hx'
    obtain ⟨d, hd⟩ := exists_diagU_of_isDiag hgdiag
    have hg25 : (g : GL (Fin 5) K) ^ 25 = 1 := by
      have : g ^ 25 = 1 := by
        apply ψ.injective
        rw [map_pow, hgx, map_one]
        exact hFt25 x hx
      have h2 := congrArg (fun y : ↥(SU5 f K) => (y : GL (Fin 5) K)) this
      simpa using h2
    have hd25 : ∀ i, d i ^ 25 = 1 := by
      intro i
      have h1 : diagU (d ^ 25) = 1 := by rw [← diagU_pow, hd, hg25]
      have h2 : d ^ 25 = 1 := diagU_injective (h1.trans diagU_one.symm)
      exact congrFun h2 i
    have hdprod : ∏ i, d i = 1 := by
      have hdet := ((mem_unitarySU_iff hU).mp g.2).1
      rw [← hd, det_diagU] at hdet
      exact Units.ext (by rw [Units.coe_prod, Units.val_one]; exact hdet)
    have hd5 : ∀ i j, d i ^ 5 = d j ^ 5 := by
      have hg5 : g ^ 5 = x ^ 5 := by
        have h1 : ψ (g ^ 5) = ψ (x ^ 5) := by rw [map_pow, hgx, hψZ _ (hxZ x hx)]
        exact ψ.injective h1
      have hg5mem : (g : GL (Fin 5) K) ^ 5 ∈ StatedScalars (Fin 5) K := by
        have h2 : ((x ^ 5 : ↥(SU5 f K)) : GL (Fin 5) K) ∈ StatedScalars (Fin 5) K := hxZ x hx
        rw [← hg5] at h2
        simpa using h2
      obtain ⟨c, hc⟩ := hg5mem
      have h3 : diagU (d ^ 5) = diagU (fun _ => c) := by
        rw [← diagU_pow, hd, ← hc, scalar_eq_diagU]
      have h4 : d ^ 5 = fun _ => c := diagU_injective h3
      intro i j
      have hi := congrFun h4 i
      have hj := congrFun h4 j
      simp only [Pi.pow_apply] at hi hj
      rw [hi, hj]
    have hgTM : g ∈ TM := Subgroup.mem_subgroupOf.2 ⟨d, ⟨hd25, hdprod, hd5⟩, hd⟩
    exact ⟨g, hgTM, hgx⟩
  have hVcomm : ∀ x ∈ Vt, ∀ y ∈ Vt, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hTMcomm a b ha hb]
  have hV5 : ∀ x ∈ Vt, x ^ 5 ∈ ZSU5 f K := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    show ψ (a ^ 5) ∈ ZSU5 f K
    rw [hψZ _ (hTM5 a ha)]
    exact hTM5 a ha
  have hVtcard : 5 ^ 4 < Nat.card Vt := by
    have h1 : Nat.card Vt = Nat.card TM := Subgroup.card_map_of_injective ψ.injective
    have h2 : Nat.card TM = Nat.card TV :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTVle).toEquiv
    have h3 : Nat.card TV = Nat.card (torusVec25 K) :=
      Subgroup.card_map_of_injective diagU_injective
    have hrK' : 5 ∣ Nat.card Kˣ := hrK
    rw [h1, h2, h3]
    exact pow_four_lt_card_torusVec25 hrK' hξ
  refine ⟨Vt.map πY, ?_, ?_, Subgroup.map_mono hFtV, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 5 ∈ πY.ker := by rw [hker]; exact hV5 x hx
    exact this
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hVcomm x hx y hy]
  · have h1 := Subgroup.card_ker_mul_card_range (πY.comp Vt.subtype)
    have hrange : (πY.comp Vt.subtype).range = Vt.map πY := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange] at h1
    have hkerle : Nat.card (πY.comp Vt.subtype).ker ≤ 5 := by
      have hinj : Function.Injective (fun x : (πY.comp Vt.subtype).ker =>
          (⟨((x : ↥Vt) : ↥(SU5 f K)), by
            have := x.2
            rw [MonoidHom.mem_ker] at this
            rw [← hker]
            exact this⟩ : ZSU5 f K)) := by
        intro x y hxy
        have h := congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext h)
      calc Nat.card (πY.comp Vt.subtype).ker ≤ Nat.card (ZSU5 f K) :=
            Nat.card_le_card_of_injective _ hinj
        _ = 5 := hZMcard
    have h2 : 5 ^ 4 < 5 * Nat.card (Vt.map πY) := by
      calc 5 ^ 4 < Nat.card Vt := hVtcard
        _ = Nat.card (πY.comp Vt.subtype).ker * Nat.card (Vt.map πY) := h1.symm
        _ ≤ 5 * Nat.card (Vt.map πY) := Nat.mul_le_mul_right _ hkerle
    omega

end CFSG.RankThree.PartOne.Q1327C
