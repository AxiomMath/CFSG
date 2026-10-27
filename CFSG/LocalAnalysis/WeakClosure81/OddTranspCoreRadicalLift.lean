module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalDefs
public import CFSG.Timmesfeld.Bridge.Asc72Defs
import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsGrp
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreStarLift
import CFSG.GroupTheory.ComapCenterPerfectQuotient

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreRadical

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Timmesfeld.Bridge.Asc72 (IsOddTransp)

variable {Y : Type} [Group Y] [Finite Y] {t : Y}

omit [Finite Y] in
theorem orderOf_mul_mem_of_mk_center (hodd : IsOddTransp {x : Y | IsConj t x}) {d e : Y}
    (hd : IsConj t d) (he : IsConj t e)
    (h : orderOf ((QuotientGroup.mk d : Y ⧸ Subgroup.center Y) * QuotientGroup.mk e) ∈
      ({1, 2, 3} : Set ℕ)) :
    orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) :=
  CoreStar.orderOf_mul_mem_of_map_of_ker_le_center (QuotientGroup.mk' (Subgroup.center Y))
    (QuotientGroup.ker_mk' _).le hodd hd he h

omit [Finite Y] in
theorem hasCoreStar_of_mk_center (hodd : IsOddTransp {x : Y | IsConj t x})
    (h : CoreStar.HasCoreStar (Y ⧸ Subgroup.center Y) (QuotientGroup.mk t)) :
    CoreStar.HasCoreStar Y t :=
  CoreStar.hasCoreStar_of_map_of_ker_le_center (QuotientGroup.mk' (Subgroup.center Y))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le hodd h

private theorem normalClosure_eq_top_of_eq_map {G : Type} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) (tH : ↥H)
    (hH : H = (Subgroup.normalClosure ({⟨(tH : G), hHK tH.2⟩} : Set ↥K)).map K.subtype)
    (hconj : ∀ k ∈ K, ∃ h ∈ H, k * (tH : G) * k⁻¹ = h * (tH : G) * h⁻¹) :
    Subgroup.normalClosure ({tH} : Set ↥H) = ⊤ := by
  set M : Subgroup G := (Subgroup.normalClosure ({tH} : Set ↥H)).map H.subtype with hM
  have hMH : M ≤ H := Subgroup.map_subtype_le _
  have hnorm : Subgroup.normalClosure ({⟨(tH : G), hHK tH.2⟩} : Set ↥K) ≤ M.comap K.subtype := by
    intro x hx
    refine Subgroup.closure_le _ |>.mpr ?_ hx
    intro y hy
    simp only [Group.conjugatesOfSet, Set.mem_iUnion, Set.mem_singleton_iff] at hy
    obtain ⟨a, ha, hy⟩ := hy
    rw [ha, conjugatesOf, Set.mem_setOf_eq] at hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hy
    obtain ⟨h, hh, hh'⟩ := hconj (c : G) c.2
    refine Subgroup.mem_comap.mpr ?_
    show (y : G) ∈ M
    rw [show (y : G) = (c : G) * (tH : G) * (c : G)⁻¹ from (congrArg Subtype.val hc).symm, hh']
    exact Subgroup.mem_map.mpr ⟨_, Subgroup.Normal.conj_mem
      (Subgroup.normalClosure_normal (s := ({tH} : Set ↥H))) tH
      (Subgroup.subset_normalClosure (s := ({tH} : Set ↥H)) rfl) ⟨h, hh⟩, rfl⟩
  have hHM : H ≤ M := by
    rw [hH]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_comap.mp (hnorm hz)
  have hMeq : M = H := le_antisymm hMH hHM
  have hinj : Function.Injective (Subgroup.map H.subtype) :=
    Subgroup.map_injective H.subtype_injective
  apply hinj
  rw [hM] at hMeq
  rw [Subgroup.map_top, Subgroup.range_subtype]
  exact hMeq

private theorem fusionZStar_eq_center_of_fusionOddCore_eq_bot {X : Type} [Group X]
    (h : fusionOddCore X = ⊥) : fusionZStar X = Subgroup.center X := by
  have hinj : Function.Injective (QuotientGroup.mk' (fusionOddCore X)) := by
    intro a b hab
    have h1 : (QuotientGroup.mk' (fusionOddCore X)) (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h1' : (↑(a⁻¹ * b) : X ⧸ fusionOddCore X) = 1 := by
      simpa [QuotientGroup.mk'_apply] using h1
    rw [QuotientGroup.eq_one_iff, h, Subgroup.mem_bot] at h1'
    exact inv_mul_eq_one.mp h1'
  refine le_antisymm (Subgroup.comap_center_le_center hinj) ?_
  intro x hx
  show QuotientGroup.mk' (fusionOddCore X) x ∈ Subgroup.center (X ⧸ fusionOddCore X)
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (fusionOddCore X) y
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]

private structure LhSetup (L : Subgroup (Y ⧸ Subgroup.center Y)) where
  P : Subgroup Y
  htP : t ∈ P
  hP : P = L.comap (QuotientGroup.mk' (Subgroup.center Y))
  Lh : Subgroup Y
  htLh : t ∈ Lh
  hLhP : Lh ≤ P
  hLh_def : Lh = (Subgroup.normalClosure ({⟨t, htP⟩} : Set ↥P)).map P.subtype
  hmapLh : Lh.map (QuotientGroup.mk' (Subgroup.center Y)) = L
  φ : ↥Lh →* ↥L
  hφ : Function.Surjective φ
  hφ_val : ∀ x : ↥Lh, ((φ x : ↥L) : Y ⧸ Subgroup.center Y) =
    (QuotientGroup.mk' (Subgroup.center Y)) (x : Y)

private def lhSetup
    {L : Subgroup (Y ⧸ Subgroup.center Y)}
    (htL : (QuotientGroup.mk t : Y ⧸ Subgroup.center Y) ∈ L)
    (hncl : Subgroup.normalClosure ({⟨_, htL⟩} : Set ↥L) = ⊤) :
    LhSetup (t := t) L := by
  let π : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' (Subgroup.center Y)
  let P : Subgroup Y := L.comap π
  have htP : t ∈ P := by
    show π t ∈ L
    simpa [π] using htL
  let S : Set ↥P := {⟨t, htP⟩}
  let N : Subgroup ↥P := Subgroup.normalClosure S
  let Lh : Subgroup Y := N.map P.subtype
  have hLh_def : Lh = (Subgroup.normalClosure ({⟨t, htP⟩} : Set ↥P)).map P.subtype := rfl
  have htLh : t ∈ Lh :=
    Subgroup.mem_map.mpr ⟨⟨t, htP⟩, Subgroup.subset_normalClosure (s := S) rfl, rfl⟩
  have hLhP : Lh ≤ P := Subgroup.map_subtype_le _
  let g : ↥P →* ↥L :=
    { toFun := fun x => ⟨π (x : Y), x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) (y : Y ⧸ Subgroup.center Y)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show π x ∈ L
      rw [show π x = (y : Y ⧸ Subgroup.center Y) from hx]
      exact y.2
    · exact Subtype.ext hx
  have hmapLh : Lh.map π = L := by
    have hcomp : L.subtype.comp g = π.comp P.subtype := by ext x; rfl
    have h1 : N.map g = Subgroup.normalClosure (g '' S) :=
      Subgroup.map_normalClosure S g hg
    have h2 : g '' S = ({⟨QuotientGroup.mk t, htL⟩} : Set ↥L) := by
      rw [Set.image_singleton,
        show g ⟨t, htP⟩ = ⟨QuotientGroup.mk t, htL⟩ from Subtype.ext rfl]
    have hstep : Lh.map π = (N.map g).map L.subtype := by
      rw [hLh_def, Subgroup.map_map, ← hcomp]
      exact (Subgroup.map_map N L.subtype g).symm
    rw [hstep, h1, h2, hncl, Subgroup.map_top, Subgroup.range_subtype]
  let φ : ↥Lh →* ↥L :=
    { toFun := fun x => ⟨π (x : Y), Subgroup.mem_comap.mp (hLhP x.2)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hφ : Function.Surjective φ := by
    intro y
    have hy : (y : Y ⧸ Subgroup.center Y) ∈ Lh.map π := by rw [hmapLh]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hφ_val : ∀ x : ↥Lh, ((φ x : ↥L) : Y ⧸ Subgroup.center Y) =
      (QuotientGroup.mk' (Subgroup.center Y)) (x : Y) := fun x => rfl
  exact { P := P, htP := htP, hP := rfl, Lh := Lh, htLh := htLh, hLhP := hLhP,
          hLh_def := hLh_def, hmapLh := hmapLh, φ := φ, hφ := hφ, hφ_val := hφ_val }

omit [Finite Y] in
private lemma LhSetup.normalClosure_eq_top
    {L : Subgroup (Y ⧸ Subgroup.center Y)}
    (S : LhSetup (t := t) L) :
    Subgroup.normalClosure ({⟨t, S.htLh⟩} : Set ↥S.Lh) = ⊤ := by
  let π : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' (Subgroup.center Y)
  have hconjP : ∀ k ∈ S.P, ∃ l ∈ S.Lh, k * t * k⁻¹ = l * t * l⁻¹ := by
    intro k hk
    have hkL : π k ∈ L := by
      rw [← Subgroup.mem_comap]
      rw [← S.hP]
      exact hk
    have hmem : π k ∈ S.Lh.map π := by
      rw [show S.Lh.map π = L from S.hmapLh]
      exact hkL
    obtain ⟨l, hl, hlk⟩ := Subgroup.mem_map.mp hmem
    refine ⟨l, hl, ?_⟩
    have hz : k * l⁻¹ ∈ Subgroup.center Y := by
      have h2 : π (k * l⁻¹) = 1 := by rw [map_mul, map_inv, hlk, mul_inv_cancel]
      have h1 : (QuotientGroup.mk (k * l⁻¹) : Y ⧸ Subgroup.center Y) = 1 := by
        simpa [π, QuotientGroup.mk'_apply] using h2
      exact (QuotientGroup.eq_one_iff (k * l⁻¹)).mp h1
    have hkey : ∀ z : Y, z ∈ Subgroup.center Y → ∀ l : Y,
        (l * z) * t * (l * z)⁻¹ = l * t * l⁻¹ := by
      intro z hzc l
      have h1 : z * t = t * z := (Subgroup.mem_center_iff.mp hzc t).symm
      have h2 : z * l = l * z := (Subgroup.mem_center_iff.mp hzc l).symm
      calc (l * z) * t * (l * z)⁻¹ = l * (z * t) * z⁻¹ * l⁻¹ := by group
        _ = l * (t * z) * z⁻¹ * l⁻¹ := by rw [h1]
        _ = l * t * l⁻¹ := by group
    have hk_eq : k = l * (k * l⁻¹) := by
      rw [Subgroup.mem_center_iff.mp hz l]; group
    rw [hk_eq]
    exact hkey (k * l⁻¹) hz l
  have hHgen : S.Lh = (Subgroup.normalClosure
      ({⟨((⟨t, S.htLh⟩ : ↥S.Lh) : Y),
        S.hLhP (⟨t, S.htLh⟩ : ↥S.Lh).2⟩} : Set ↥S.P)).map S.P.subtype := by
    conv_lhs => rw [S.hLh_def]
  exact normalClosure_eq_top_of_eq_map S.hLhP ⟨t, S.htLh⟩ hHgen hconjP

omit [Finite Y] in
private lemma LhSetup.ker_le_center {L : Subgroup (Y ⧸ Subgroup.center Y)}
    (S : LhSetup (t := t) L) :
    S.φ.ker ≤ Subgroup.center ↥S.Lh := by
  intro z hz
  have hz1 : S.φ z = 1 := MonoidHom.mem_ker.mp hz
  have hzπ : (QuotientGroup.mk' (Subgroup.center Y)) (z : Y) = 1 := by
    have h' := congrArg Subtype.val hz1
    rw [S.hφ_val z] at h'
    simpa using h'
  have hzY : (z : Y) ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff (z : Y)).mp hzπ
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  simpa using Subgroup.mem_center_iff.mp hzY (w : Y)

omit [Finite Y] in
private lemma not_fusionOddCore_map_top
    {L : Subgroup (Y ⧸ Subgroup.center Y)}
    (htL : (QuotientGroup.mk t : Y ⧸ Subgroup.center Y) ∈ L)
    (hncl : Subgroup.normalClosure ({⟨_, htL⟩} : Set ↥L) = ⊤)
    {n : ℕ} (h : IsL2OrSz (↥L ⧸ Subgroup.center ↥L) n) (ht : t ^ 2 = 1)
    {Lh : Subgroup Y} (ψ : ↥Lh →* (↥L ⧸ Subgroup.center ↥L))
    (hOodd : Odd (Nat.card ↥(fusionOddCore ↥Lh)))
    (htop : (fusionOddCore ↥Lh).map ψ = ⊤) :
    False := by
  have hsurj : Function.Surjective (ψ.comp (fusionOddCore ↥Lh).subtype) := by
    intro a
    have ha : a ∈ (fusionOddCore ↥Lh).map ψ := by rw [htop]; exact Subgroup.mem_top a
    obtain ⟨v, hv, hva⟩ := Subgroup.mem_map.mp ha
    exact ⟨⟨v, hv⟩, hva⟩
  obtain ⟨e⟩ := QuotientGroup.quotientKerEquivOfSurjective
    (ψ.comp (fusionOddCore ↥Lh).subtype) hsurj
  have hcard : Nat.card ↥(fusionOddCore ↥Lh) =
      Nat.card (↥L ⧸ Subgroup.center ↥L) *
        Nat.card ↥((ψ.comp (fusionOddCore ↥Lh).subtype).ker) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup, Nat.card_congr e]
  have hOddG : Odd (Nat.card (↥L ⧸ Subgroup.center ↥L)) :=
    hOodd.of_dvd_nat ⟨_, by rw [hcard, mul_comm]⟩
  let x : ↥L := ⟨QuotientGroup.mk t, htL⟩
  let u : ↥L ⧸ Subgroup.center ↥L := (QuotientGroup.mk' (Subgroup.center ↥L)) x
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    have hxval : (↑x : Y ⧸ Subgroup.center Y) = QuotientGroup.mk t := rfl
    rw [hxval, ← QuotientGroup.mk_pow (Subgroup.center Y) t 2, ht]
    simp
  have hu2 : u ^ 2 = 1 := by
    have huval : u = (QuotientGroup.mk' (Subgroup.center ↥L)) x := rfl
    rw [huval, ← map_pow, hx2, map_one]
  have hu_ne : u ≠ 1 := by
    intro hu1
    have hu1' : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) = 1 := by
      simpa [u, QuotientGroup.mk'_apply] using hu1
    have hxZ : x ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff x).mp hu1'
    have hle : (⊤ : Subgroup ↥L) ≤ Subgroup.center ↥L := by
      rw [← hncl]
      apply Subgroup.normalClosure_le_normal
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hxZ
    have htop : Subgroup.center ↥L = ⊤ := le_antisymm le_top hle
    have hsub : Subsingleton (↥L ⧸ Subgroup.center ↥L) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have hnt : Nontrivial (↥L ⧸ Subgroup.center ↥L) :=
      @IsSimpleGroup.toNontrivial _ _ (CFSG.Quasithin.E2.isSimpleGroup_of_psl_or_sz h)
    exact (not_subsingleton_iff_nontrivial.mpr hnt) hsub
  have hu_order : orderOf u = 2 := orderOf_eq_prime hu2 hu_ne
  have hdvd : orderOf u ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := orderOf_dvd_natCard u
  have h2dvd : 2 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rw [← hu_order]
    exact hdvd
  exact (Nat.not_even_iff_odd.mpr hOddG) (even_iff_two_dvd.mpr h2dvd)

omit [Finite Y] in
private lemma fusionOddCore_eq_bot_of_map
    {L : Subgroup (Y ⧸ Subgroup.center Y)}
    (S : LhSetup (t := t) L)
    (hZ : Nat.card ↥(Subgroup.center ↥L) ∣ 2)
    (hOmap : (fusionOddCore ↥S.Lh).map ((QuotientGroup.mk' (Subgroup.center ↥L)).comp S.φ) = ⊥)
    (hCker : (Subgroup.center ↥L).comap S.φ =
      ((QuotientGroup.mk' (Subgroup.center ↥L)).comp S.φ).ker)
    (hOodd : Odd (Nat.card ↥(fusionOddCore ↥S.Lh)))
    (hO : fusionOddCore Y = ⊥) :
    fusionOddCore ↥S.Lh = ⊥ := by
  let π : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' (Subgroup.center Y)
  have hOleC : fusionOddCore ↥S.Lh ≤ (Subgroup.center ↥L).comap S.φ := by
    rw [Subgroup.map_eq_bot_iff] at hOmap
    rw [← hCker] at hOmap
    exact hOmap
  have hOπ : ∀ v ∈ fusionOddCore ↥S.Lh, S.φ v = 1 := by
    intro v hv
    have hvZ : S.φ v ∈ Subgroup.center ↥L := Subgroup.mem_comap.mp (hOleC hv)
    have hdvd2 : orderOf (S.φ v) ∣ 2 :=
      (Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hvZ).trans hZ
    have hdvdO : orderOf (S.φ v) ∣ orderOf v := orderOf_map_dvd S.φ v
    have hoddx : Odd (orderOf v) :=
      hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard (fusionOddCore ↥S.Lh) hv)
    have hodd : Odd (orderOf (S.φ v)) := hoddx.of_dvd_nat hdvdO
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hodd
      obtain ⟨k, hk⟩ := hodd
      omega
  have hObot : fusionOddCore ↥S.Lh = ⊥ := by
    have hOZ : (fusionOddCore ↥S.Lh).map S.Lh.subtype ≤ Subgroup.center Y := by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
      have h1 : π (v : Y) = 1 := by
        have h' := congrArg Subtype.val (hOπ v hv)
        rw [S.hφ_val v] at h'
        simpa [π] using h'
      exact (QuotientGroup.eq_one_iff (v : Y)).mp h1
    have hnorm : ((fusionOddCore ↥S.Lh).map S.Lh.subtype).Normal := by
      refine Subgroup.Normal.mk fun n hn g => ?_
      have hc := Subgroup.mem_center_iff.mp (hOZ hn) g
      rw [show g * n * g⁻¹ = n by rw [hc]; group]
      exact hn
    have hOddN : Odd (Nat.card ↥((fusionOddCore ↥S.Lh).map S.Lh.subtype)) := by
      rw [Subgroup.card_map_of_injective S.Lh.subtype_injective]
      exact hOodd
    have hle : (fusionOddCore ↥S.Lh).map S.Lh.subtype ≤ fusionOddCore Y :=
      le_sSup ⟨hnorm, hOddN⟩
    rw [hO] at hle
    have h2 := Subgroup.map_eq_bot_iff (fusionOddCore ↥S.Lh) (f := S.Lh.subtype) |>.mp
      (le_bot_iff.mp hle)
    rw [Subgroup.ker_subtype] at h2
    exact le_bot_iff.mp h2
  exact hObot

theorem exists_L2OrSz_of_mk_center (hO : fusionOddCore Y = ⊥) (ht : t ^ 2 = 1)
    {L : Subgroup (Y ⧸ Subgroup.center Y)}
    (htL : (QuotientGroup.mk t : Y ⧸ Subgroup.center Y) ∈ L)
    (hncl : Subgroup.normalClosure ({⟨_, htL⟩} : Set ↥L) = ⊤)
    (hZ : Nat.card ↥(Subgroup.center ↥L) ∣ 2) {n : ℕ} (hn : 1 < n)
    (h : IsL2OrSz (↥L ⧸ Subgroup.center ↥L) n) :
    ∃ Lh : Subgroup Y, ∃ htLh : t ∈ Lh,
      Subgroup.normalClosure ({⟨t, htLh⟩} : Set ↥Lh) = ⊤ ∧
      IsL2OrSz (↥Lh ⧸ fusionZStar ↥Lh) n := by
  classical
  obtain S := lhSetup htL hncl
  let ψ : ↥S.Lh →* (↥L ⧸ Subgroup.center ↥L) :=
    (QuotientGroup.mk' (Subgroup.center ↥L)).comp S.φ
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).comp S.hφ
  have hnclLh : Subgroup.normalClosure ({⟨t, S.htLh⟩} : Set ↥S.Lh) = ⊤ :=
    S.normalClosure_eq_top
  have hker : S.φ.ker ≤ Subgroup.center ↥S.Lh := S.ker_le_center
  have hGperf : commutator (↥L ⧸ Subgroup.center ↥L) = ⊤ :=
    CFSG.Quasithin.E2.commutator_eq_top_of_psl_or_sz hn h
  have hCeq : Subgroup.center ↥S.Lh = (Subgroup.center ↥L).comap S.φ :=
    (CFSG.GroupTheory.comap_center_eq_center_of_card_center_dvd_two S.φ S.hφ hker hZ
      hGperf).symm
  have hOodd : Odd (Nat.card ↥(fusionOddCore ↥S.Lh)) :=
    Nat.coprime_two_left.mp (CFSG.LargeExtraspecial.S9.coprime_card_fusionOddCore (K := ↥S.Lh))
  have hOmap : (fusionOddCore ↥S.Lh).map ψ = ⊥ := by
    rcases @Subgroup.Normal.eq_bot_or_eq_top _ _
      (CFSG.Quasithin.E2.isSimpleGroup_of_psl_or_sz h)
      (Subgroup.map ψ (fusionOddCore ↥S.Lh))
      (Subgroup.Normal.map (fusionOddCore_normal ↥S.Lh) ψ hψ) with hbot | htop
    · exact hbot
    · exfalso
      exact not_fusionOddCore_map_top htL hncl h ht ψ hOodd htop
  have hCker : (Subgroup.center ↥L).comap S.φ = ψ.ker := by
    ext x
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (S.φ x)).symm
  have hObot : fusionOddCore ↥S.Lh = ⊥ :=
    fusionOddCore_eq_bot_of_map S hZ hOmap hCker hOodd hO
  have hZstar : fusionZStar ↥S.Lh = Subgroup.center ↥S.Lh :=
    fusionZStar_eq_center_of_fusionOddCore_eq_bot hObot
  have hkerψ : ψ.ker = Subgroup.center ↥S.Lh := by
    rw [← hCker, ← hCeq]
  refine ⟨S.Lh, S.htLh, hnclLh, ?_⟩
  exact isL2OrSz_of_mulEquiv h ((QuotientGroup.quotientMulEquivOfEq
    (hZstar.trans hkerψ.symm)).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).symm

theorem radicalOutcome_lift (hO : fusionOddCore Y = ⊥) (hodd : IsOddTransp {x : Y | IsConj t x})
    (h : RadicalOutcome (Y ⧸ Subgroup.center Y) (QuotientGroup.mk t)) :
    CoreStar.HasCoreStar Y t ∨
      ∃ Lh : Subgroup Y, ∃ htLh : t ∈ Lh,
        Subgroup.normalClosure ({⟨t, htLh⟩} : Set ↥Lh) = ⊤ ∧
        ∃ n : ℕ, 1 < n ∧ IsL2OrSz (↥Lh ⧸ fusionZStar ↥Lh) n := by
  rcases h with hstar | ⟨L, htL, hncl, hZ, n, hn, hL⟩
  · exact Or.inl (hasCoreStar_of_mk_center hodd hstar)
  · obtain ⟨Lh, htLh, hncl', hL2⟩ :=
      exists_L2OrSz_of_mk_center hO (by
        have h2 : orderOf t = 2 := hodd.1 t (IsConj.refl t)
        simpa [h2] using pow_orderOf_eq_one t) htL hncl hZ hn hL
    exact Or.inr ⟨Lh, htLh, hncl', n, hn, hL2⟩

end CFSG.LocalAnalysis.WeakClosure81.CoreRadical
