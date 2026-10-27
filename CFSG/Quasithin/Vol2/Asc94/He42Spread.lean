module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec2
public import CFSG.Quasithin.Vol2.Asc94.He42FinA

public section

namespace CFSG.Quasithin.A94.He42

open scoped Matrix
open Subgroup CFSG.Quasithin.A94.HeJ CFSG.Quasithin.A94.He42PD

variable {G : Type} [Group G] [Finite G]

private theorem he42sp_conj_y {L A Z : Subgroup G} {y g : G}
    (hyL : y ∈ normalizer (L : Set G)) (hcomm : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ A)
    (hAab : ∀ x ∈ A, ∀ x' ∈ A, x * x' = x' * x) (hZA : Z ≤ A)
    (hyZ : ∀ w ∈ Z, y * w * y⁻¹ ∈ Z) (hgL : g ∈ L) {z : G} (hgz : g * z * g⁻¹ ∈ Z) :
    g * (y * z * y⁻¹) * g⁻¹ ∈ Z := by
  have hg'L : y⁻¹ * g * y ∈ L := by
    refine (mem_normalizer_iff.mp hyL (y⁻¹ * g * y)).mpr ?_
    have e : y * (y⁻¹ * g * y) * y⁻¹ = g := by group
    rw [e]
    exact hgL
  have ha : (y⁻¹ * g * y) * g⁻¹ ∈ A := by
    have h := hcomm _ hg'L
    have e : y * (y⁻¹ * g * y) * y⁻¹ * (y⁻¹ * g * y)⁻¹ = g * (y⁻¹ * g * y)⁻¹ := by group
    rw [e] at h
    have e2 : (g * (y⁻¹ * g * y)⁻¹)⁻¹ = (y⁻¹ * g * y) * g⁻¹ := by group
    rw [← e2]
    exact A.inv_mem h
  have hconj : (y⁻¹ * g * y) * z * (y⁻¹ * g * y)⁻¹ = g * z * g⁻¹ := by
    have hzA : g * z * g⁻¹ ∈ A := hZA hgz
    obtain ⟨a, ha_def⟩ : ∃ a, a = (y⁻¹ * g * y) * g⁻¹ := ⟨_, rfl⟩
    have haA : a ∈ A := by rw [ha_def]; exact ha
    have e1 : y⁻¹ * g * y = a * g := by rw [ha_def]; group
    rw [e1]
    have e2 : a * g * z * (a * g)⁻¹ = a * (g * z * g⁻¹) * a⁻¹ := by group
    rw [e2, hAab a haA _ hzA]
    group
  have e3 : g * (y * z * y⁻¹) * g⁻¹ = y * ((y⁻¹ * g * y) * z * (y⁻¹ * g * y)⁻¹) * y⁻¹ := by
    group
  rw [e3, hconj]
  exact hyZ _ hgz

private theorem he42sp_fin4_key {B : Subgroup G} {u v : G} (hu2 : u * u = 1) (hv2 : v * v = 1)
    (huv : u * v = v * u) (h1 : u ∉ B) (h2 : v ∉ B) (h3 : u * v ∉ B) :
    ∀ i j : Fin 4, (![1, u, v, u * v] i)⁻¹ * ![1, u, v, u * v] j ∈ B → i = j := by
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have huv' : (u * v)⁻¹ = u * v := by
    rw [mul_inv_rev, hu, hv]
    exact huv.symm
  have e1 : v * (u * v) = u := by rw [← mul_assoc, ← huv, mul_assoc, hv2, mul_one]
  have e2 : u * (u * v) = v := by rw [← mul_assoc, hu2, one_mul]
  have e3 : u * v * u = v := by rw [huv, mul_assoc, hu2, mul_one]
  have e4 : u * v * v = u := by rw [mul_assoc, hv2, mul_one]
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [hu, hv, huv', e1, e2, e3, e4, huv.symm] at hij ⊢ <;>
    first
    | exact absurd hij h1
    | exact absurd hij h2
    | exact absurd hij h3
    | rfl

private theorem he42sp_eq_top_of_four {Z B X : Subgroup G} (hXZ : X ≤ Z) (hBX : B ≤ X)
    (hZc : Nat.card ↥Z = 16) (hBc : Nat.card ↥B = 4) (xs : Fin 4 → G) (hxs : ∀ i, xs i ∈ X)
    (hkey : ∀ i j : Fin 4, (xs i)⁻¹ * xs j ∈ B → i = j) : X = Z := by
  have hinj : Function.Injective
      (fun p : Fin 4 × ↥B => (⟨xs p.1 * p.2, X.mul_mem (hxs p.1) (hBX p.2.2)⟩ : ↥X)) := by
    rintro ⟨i, b⟩ ⟨j, b'⟩ h
    have h' : xs i * b.1 = xs j * b'.1 := congrArg Subtype.val h
    have e : (xs j)⁻¹ * xs i = b'.1 * b.1⁻¹ := by
      calc (xs j)⁻¹ * xs i = (xs j)⁻¹ * (xs i * b.1) * b.1⁻¹ := by group
        _ = (xs j)⁻¹ * (xs j * b'.1) * b.1⁻¹ := by rw [h']
        _ = b'.1 * b.1⁻¹ := by group
    have hji : j = i := hkey j i (by rw [e]; exact B.mul_mem b'.2 (B.inv_mem b.2))
    subst hji
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h'))
  have hle : Nat.card (Fin 4 × ↥B) ≤ Nat.card ↥X := Nat.card_le_card_of_injective _ hinj
  have hcard : Nat.card (Fin 4 × ↥B) = 16 := by
    rw [Nat.card_prod, hBc]
    simp
  rw [hcard] at hle
  exact Subgroup.eq_of_le_of_card_ge hXZ (by rw [hZc]; exact hle)

private theorem he42sp_all_norm {L K A J Z : Subgroup G} {ψ : ↥L →* Equiv.Perm (Fin 5)}
    (hPD : PData L K A J ψ) (hKZ : ∀ k ∈ K, ∀ z ∈ Z, k * z * k⁻¹ ∈ Z)
    {g : G} (hgL : g ∈ L) (hgK : g ∉ K) (hgZ : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z) :
    ∀ l ∈ L, ∀ z ∈ Z, l * z * l⁻¹ ∈ Z := by
  classical
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, W = L ⊓ normalizer (Z : Set G) := ⟨_, rfl⟩
  have hWmem : ∀ x, x ∈ W ↔ x ∈ L ∧ ∀ z ∈ Z, x * z * x⁻¹ ∈ Z := by
    intro x
    rw [hWdef, Subgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun z hz => (mem_normalizer_iff.mp h2 z).mp hz⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Subgroup.mem_normalizer_fintype (fun n hn => h2 n hn)⟩
  have hKW : ∀ k ∈ K, k ∈ W := fun k hk => (hWmem k).mpr ⟨hPD.KL hk, hKZ k hk⟩
  have hgW : g ∈ W := (hWmem g).mpr ⟨hgL, hgZ⟩
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : Subgroup (Equiv.Perm (Fin 5)), Ψ = (W.subgroupOf L).map ψ :=
    ⟨_, rfl⟩
  have hmemS : ∀ σ : Equiv.Perm (Fin 5), σ ∈ CFSG.Quasithin.A94.He42Fin.Stab0 ↔
      σ ∈ alternatingGroup (Fin 5) ∧ σ 0 = 0 := by
    intro σ
    simp only [CFSG.Quasithin.A94.He42Fin.Stab0, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      Equiv.Perm.smul_def]
  have hΨle : Ψ ≤ alternatingGroup (Fin 5) := by
    rw [hΨdef]
    rintro _ ⟨x, -, rfl⟩
    rw [← hPD.range]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hStab : CFSG.Quasithin.A94.He42Fin.Stab0 ≤ Ψ := by
    intro σ hσ
    obtain ⟨hσA, hσ0⟩ := (hmemS σ).mp hσ
    have hσr : σ ∈ ψ.range := by rw [hPD.range]; exact hσA
    obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hσr
    have hlK : (l : G) ∈ K := (hPD.stab l).mp (by rw [hl]; exact hσ0)
    rw [hΨdef]
    exact Subgroup.mem_map.mpr ⟨l, Subgroup.mem_subgroupOf.mpr (hKW _ hlK), hl⟩
  have hgΨ : ψ ⟨g, hgL⟩ ∈ Ψ := by
    rw [hΨdef]
    exact Subgroup.mem_map.mpr ⟨⟨g, hgL⟩, Subgroup.mem_subgroupOf.mpr hgW, rfl⟩
  have hne : Ψ ≠ CFSG.Quasithin.A94.He42Fin.Stab0 := by
    intro h
    rw [h] at hgΨ
    have h2 : ψ ⟨g, hgL⟩ 0 = 0 := ((hmemS _).mp hgΨ).2
    exact hgK ((hPD.stab ⟨g, hgL⟩).mp h2)
  have hΨtop : Ψ = alternatingGroup (Fin 5) :=
    (CFSG.Quasithin.A94.He42Fin.stab0_maximal Ψ hΨle hStab).resolve_left hne
  intro l hl z hz
  have hlW : l ∈ W := by
    have hmem : ψ ⟨l, hl⟩ ∈ Ψ := by
      rw [hΨtop, ← hPD.range]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rw [hΨdef] at hmem
    obtain ⟨w, hw, hwl⟩ := Subgroup.mem_map.mp hmem
    have hk : ψ (w⁻¹ * ⟨l, hl⟩) = 1 := by rw [map_mul, map_inv, hwl, inv_mul_cancel]
    have hkA : ((w⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ A := by
      have hker : w⁻¹ * ⟨l, hl⟩ ∈ ψ.ker := MonoidHom.mem_ker.mpr hk
      rw [hPD.ker, Subgroup.mem_subgroupOf] at hker
      exact hker
    have hkW : ((w⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ W := hKW _ (hPD.JK (hPD.AJ hkA))
    have hwW : (w : G) ∈ W := Subgroup.mem_subgroupOf.mp hw
    have hprod : (w : G) * ((w⁻¹ * ⟨l, hl⟩ : ↥L) : G) = l := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hm := W.mul_mem hwW hkW
    rwa [hprod] at hm
  exact ((hWmem l).mp hlW).2 z hz

private theorem he42sp_centr {L K A A' J Z R : Subgroup G} {ψ : ↥L →* Equiv.Perm (Fin 5)}
    (hPD : PData L K A J ψ) (hA'J : A' ≤ J) (hZA : Z ≤ A) (hZA' : Z ≤ A')
    (hAab : ∀ x ∈ A, ∀ x' ∈ A, x * x' = x' * x) (hA'ab : ∀ x ∈ A', ∀ x' ∈ A', x * x' = x' * x)
    (hall : ∀ l ∈ L, ∀ z ∈ Z, l * z * l⁻¹ ∈ Z)
    (hRA' : R ≤ A') (hRc : Nat.card ↥R = 4) (hRA : A ⊓ R = ⊥) :
    ∀ l ∈ L, ∀ z ∈ Z, l * z = z * l := by
  classical
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup G, D = L ⊓ centralizer (Z : Set G) := ⟨_, rfl⟩
  have hDmem : ∀ x, x ∈ D ↔ x ∈ L ∧ ∀ z ∈ Z, z * x = x * z := by
    intro x
    subst hDdef
    exact Iff.rfl
  have hDnorm : ∀ d ∈ D, ∀ l ∈ L, l * d * l⁻¹ ∈ D := by
    intro d hd l hl
    obtain ⟨hdL, hdC⟩ := (hDmem d).mp hd
    refine (hDmem _).mpr ⟨L.mul_mem (L.mul_mem hl hdL) (L.inv_mem hl), fun z hz => ?_⟩
    have hz' : l⁻¹ * z * l ∈ Z := by
      have h := hall l⁻¹ (L.inv_mem hl) z hz
      simpa [mul_assoc] using h
    have hdz := hdC _ hz'
    calc z * (l * d * l⁻¹) = l * ((l⁻¹ * z * l) * d) * l⁻¹ := by group
      _ = l * (d * (l⁻¹ * z * l)) * l⁻¹ := by rw [hdz]
      _ = l * d * l⁻¹ * z := by group
  have hDn : (D.subgroupOf L).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hDnorm _ hn (g : G) g.2
    simpa using h⟩
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : ↥L →* ↥(alternatingGroup (Fin 5)),
      ∀ l, (ψ' l : Equiv.Perm (Fin 5)) = ψ l :=
    ⟨ψ.codRestrict (alternatingGroup (Fin 5)) (fun l => by
      rw [← hPD.range]
      exact MonoidHom.mem_range.mpr ⟨l, rfl⟩), fun l => rfl⟩
  have hsurj : Function.Surjective ψ' := by
    intro a
    have ha : (a : Equiv.Perm (Fin 5)) ∈ ψ.range := by rw [hPD.range]; exact a.2
    obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp ha
    exact ⟨l, Subtype.ext ((hψ' l).trans hl)⟩
  haveI hMn : ((D.subgroupOf L).map ψ').Normal := hDn.map ψ' hsurj
  have hsimp : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((D.subgroupOf L).map ψ') with hbot | htop
  · exfalso
    have hRbot : R = ⊥ := by
      rw [eq_bot_iff]
      intro r hr
      have hrL : r ∈ L := hPD.KL (hPD.JK (hA'J (hRA' hr)))
      have hrD : (⟨r, hrL⟩ : ↥L) ∈ D.subgroupOf L := Subgroup.mem_subgroupOf.mpr
        ((hDmem r).mpr ⟨hrL, fun z hz => hA'ab z (hZA' hz) r (hRA' hr)⟩)
      have h2 : ψ' ⟨r, hrL⟩ ∈ (D.subgroupOf L).map ψ' := Subgroup.mem_map.mpr ⟨_, hrD, rfl⟩
      rw [hbot] at h2
      have h3 : ψ' ⟨r, hrL⟩ = 1 := Subgroup.mem_bot.mp h2
      have h4 : ψ ⟨r, hrL⟩ = 1 := by
        rw [← hψ' ⟨r, hrL⟩, h3, Subgroup.coe_one]
      have hrA : r ∈ A := by
        have hker : (⟨r, hrL⟩ : ↥L) ∈ ψ.ker := MonoidHom.mem_ker.mpr h4
        rw [hPD.ker, Subgroup.mem_subgroupOf] at hker
        exact hker
      have hr1 : r ∈ A ⊓ R := ⟨hrA, hr⟩
      rw [hRA] at hr1
      exact hr1
    rw [hRbot, Subgroup.card_bot] at hRc
    norm_num at hRc
  · intro l hl z hz
    have hlmem : ψ' ⟨l, hl⟩ ∈ (D.subgroupOf L).map ψ' := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨d, hd, hdl⟩ := Subgroup.mem_map.mp hlmem
    have hdψ : ψ d = ψ ⟨l, hl⟩ := by
      rw [← hψ' d, hdl]
      exact hψ' _
    have hkA : ((d⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ A := by
      have hker : d⁻¹ * ⟨l, hl⟩ ∈ ψ.ker :=
        MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hdψ, inv_mul_cancel])
      rw [hPD.ker, Subgroup.mem_subgroupOf] at hker
      exact hker
    have hA_D : ∀ a ∈ A, a ∈ D := fun a ha => (hDmem a).mpr
      ⟨hPD.KL (hPD.JK (hPD.AJ ha)), fun z' hz' => hAab z' (hZA hz') a ha⟩
    have hkD : ((d⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ D := hA_D _ hkA
    have hprod : (d : G) * ((d⁻¹ * ⟨l, hl⟩ : ↥L) : G) = l := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hlD : l ∈ D := by
      have hm := D.mul_mem (Subgroup.mem_subgroupOf.mp hd) hkD
      rwa [hprod] at hm
    exact (((hDmem l).mp hlD).2 z hz).symm

private theorem he42sp_side {L K A A' J B Z R : Subgroup G} {y y₀ : G}
    {ψ : ↥L →* Equiv.Perm (Fin 5)} (hPD : PData L K A J ψ)
    (hA'J : A' ≤ J) (hBZ : B ≤ Z) (hBc : Nat.card ↥B = 4) (hZc : Nat.card ↥Z = 16)
    (hZA : Z ≤ A) (hZA' : Z ≤ A')
    (hAab : ∀ x ∈ A, ∀ x' ∈ A, x * x' = x' * x) (hA'ab : ∀ x ∈ A', ∀ x' ∈ A', x * x' = x' * x)
    (hAsq : ∀ x ∈ A, x * x = 1) (hLB : ∀ l ∈ L, ∀ b ∈ B, l * b = b * l)
    (hyL : y ∈ normalizer (L : Set G)) (hcomm : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ A)
    (hy3 : y * y * y = 1) (hyZ : ∀ z ∈ Z, y * z * y⁻¹ ∈ Z) (hyB : ∀ b ∈ B, y * b * y⁻¹ ∈ B)
    (hZB : ∀ z ∈ Z, y * z * y⁻¹ * z⁻¹ ∈ B → z ∈ B)
    (hKZ : ∀ k ∈ K, ∀ z ∈ Z, k * z * k⁻¹ ∈ Z)
    (hRA' : R ≤ A') (hRc : Nat.card ↥R = 4) (hRA : A ⊓ R = ⊥)
    (hy0 : y₀ ∈ K) (hy0Z : ∃ z ∈ Z, y₀ * z * y₀⁻¹ ≠ z) :
    ∀ g ∈ L, g ∉ K → ∀ z ∈ Z, g * z * g⁻¹ ∈ Z → z ∈ B := by
  intro g hgL hgK z hz hgz
  by_contra hzB
  obtain ⟨X, hXdef⟩ : ∃ X : Subgroup G,
      X = Z ⊓ Subgroup.comap (MulAut.conj g).toMonoidHom Z := ⟨_, rfl⟩
  have hX : ∀ w, w ∈ X ↔ w ∈ Z ∧ g * w * g⁻¹ ∈ Z := by
    intro w
    subst hXdef
    exact Iff.rfl
  have hXZ : X ≤ Z := by
    intro w hw
    exact ((hX w).mp hw).1
  have hzX : z ∈ X := (hX z).mpr ⟨hz, hgz⟩
  have hz'Z : y * z * y⁻¹ ∈ Z := hyZ z hz
  have hz'X : y * z * y⁻¹ ∈ X :=
    (hX _).mpr ⟨hz'Z, he42sp_conj_y hyL hcomm hAab hZA hyZ hgL hgz⟩
  have hzsq : z * z = 1 := hAsq z (hZA hz)
  have hz'sq : (y * z * y⁻¹) * (y * z * y⁻¹) = 1 := hAsq _ (hZA hz'Z)
  have hzcomm : z * (y * z * y⁻¹) = (y * z * y⁻¹) * z := hAab z (hZA hz) _ (hZA hz'Z)
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzsq
  have F2 : y * z * y⁻¹ ∉ B := by
    intro h2
    apply hzB
    have h3 : y * (y * (y * z * y⁻¹) * y⁻¹) * y⁻¹ = z := by
      have e : y * (y * (y * z * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * z * (y * y * y)⁻¹ := by
        group
      rw [e, hy3, inv_one, one_mul, mul_one]
    have h4 := hyB _ (hyB _ h2)
    rwa [h3] at h4
  have F3 : z * (y * z * y⁻¹) ∉ B := by
    intro h3
    apply hzB
    apply hZB z hz
    rw [hzinv, ← hzcomm]
    exact h3
  have hBX : B ≤ X := by
    intro b hb
    refine (hX b).mpr ⟨hBZ hb, ?_⟩
    rw [hLB g hgL b hb, mul_inv_cancel_right]
    exact hBZ hb
  have hxs : ∀ i : Fin 4, (![1, z, y * z * y⁻¹, z * (y * z * y⁻¹)] i) ∈ X := by
    intro i
    fin_cases i
    · exact X.one_mem
    · exact hzX
    · exact hz'X
    · exact X.mul_mem hzX hz'X
  have hkey := he42sp_fin4_key (B := B) hzsq hz'sq hzcomm hzB F2 F3
  have hXeqZ : X = Z :=
    he42sp_eq_top_of_four hXZ hBX hZc hBc ![1, z, y * z * y⁻¹, z * (y * z * y⁻¹)] hxs hkey
  have hgZ : ∀ w ∈ Z, g * w * g⁻¹ ∈ Z := by
    intro w hw
    have hwX : w ∈ X := by
      rw [hXeqZ]
      exact hw
    exact ((hX w).mp hwX).2
  have hall := he42sp_all_norm hPD hKZ hgL hgK hgZ
  have hcent := he42sp_centr hPD hA'J hZA hZA' hAab hA'ab hall hRA' hRc hRA
  obtain ⟨z0, hz0, hne⟩ := hy0Z
  apply hne
  have hy0L : y₀ ∈ L := hPD.KL hy0
  have hc0 := hcent y₀ hy0L z0 hz0
  rw [hc0]
  group

private theorem he42sp_m_conj (S : HeSetup G) {y : G} (hy : y ∈ S.N) {z : G} (hz : z ∈ S.Z) :
    S.m (y * z * y⁻¹) = ((S.rhoG y).1 : M2) * S.m z * ((S.rhoG y).2 : M2)ᵀ := by
  rw [S.rhoG_of_mem hy]
  exact S.hD.hT.m_conj S.N S.hD.hK.norm ⟨y, hy⟩ hz

private theorem he42sp_yB (S : HeSetup G) {y : G} (hyN : y ∈ S.N) (hρ : S.rhoG y = (S.g, 1))
    (hyZ : ∀ z ∈ S.Z, y * z * y⁻¹ ∈ S.Z) :
    ∀ b ∈ S.B, y * b * y⁻¹ ∈ S.B := by
  intro b hb
  have hbZ : b ∈ S.Z := (Subgroup.mem_inf.mp hb).1
  have hcb : (S.g : M2) * S.m b = S.m b * (S.g : M2) :=
    ((S.hD.mem_B_iff S.hxN S.hxa S.hx3).1 hb).2
  have hm : S.m (y * b * y⁻¹) = (S.g : M2) * S.m b := by
    rw [he42sp_m_conj S hyN hbZ, hρ]
    simp
  have hc : (S.g : M2) * S.m (y * b * y⁻¹) = S.m (y * b * y⁻¹) * (S.g : M2) := by
    rw [hm]
    calc (S.g : M2) * ((S.g : M2) * S.m b) = (S.g : M2) * (S.m b * (S.g : M2)) := by rw [hcb]
      _ = (S.g : M2) * S.m b * (S.g : M2) := (mul_assoc _ _ _).symm
  exact (S.hD.mem_B_iff S.hxN S.hxa S.hx3).2 ⟨hyZ b hbZ, hc⟩

private theorem he42sp_yB2 (S : HeSetup G) {y₁ y₂ : G} (hyB : ∀ b ∈ S.B, y₁ * b * y₁⁻¹ ∈ S.B)
    (h0K : y₁ * y₂⁻¹ ∈ S.K) : ∀ b ∈ S.B, y₂ * b * y₂⁻¹ ∈ S.B := by
  intro b hb
  have hC : ∀ c ∈ S.B, c * (y₁ * y₂⁻¹) = (y₁ * y₂⁻¹) * c := fun c hc =>
    mem_centralizer_iff.mp (Subgroup.mem_inf.mp h0K).2 c hc
  have hcC := hC _ (hyB b hb)
  have e : y₂ * b * y₂⁻¹ = (y₁ * y₂⁻¹)⁻¹ * (y₁ * b * y₁⁻¹) * (y₁ * y₂⁻¹) := by group
  have e2 : (y₁ * y₂⁻¹)⁻¹ * (y₁ * b * y₁⁻¹) * (y₁ * y₂⁻¹) = y₁ * b * y₁⁻¹ := by
    calc (y₁ * y₂⁻¹)⁻¹ * (y₁ * b * y₁⁻¹) * (y₁ * y₂⁻¹)
        = (y₁ * y₂⁻¹)⁻¹ * ((y₁ * b * y₁⁻¹) * (y₁ * y₂⁻¹)) := by group
      _ = (y₁ * y₂⁻¹)⁻¹ * ((y₁ * y₂⁻¹) * (y₁ * b * y₁⁻¹)) := by rw [hcC]
      _ = y₁ * b * y₁⁻¹ := by group
  rw [e, e2]
  exact hyB b hb

theorem HeSetup.stepSpread (S : HeSetup G) (hB : S.BaseFacts) (hP : S.StepPsi) {y₁ y₂ : G}
    (hY : YSpec S y₁ y₂) (hn : S.StepYnorm y₁ y₂) (h0 : S.StepY0 y₁ y₂) (hR : S.StepR y₁ y₂)
    (hZ : S.StepZmat y₁ y₂) (hc : S.StepComm y₁ y₂) : S.StepSpread := by
  obtain ⟨ψ₁, hPD₁⟩ := hP.1
  obtain ⟨ψ₂, hPD₂⟩ := hP.2
  have hy3₁ : y₁ * y₁ * y₁ = 1 := by
    have h := pow_orderOf_eq_one y₁
    rw [hY.ord₁] at h
    exact (pow_three' y₁).symm.trans h
  have hy3₂ : y₂ * y₂ * y₂ = 1 := by
    have h := pow_orderOf_eq_one y₂
    rw [hY.ord₂] at h
    exact (pow_three' y₂).symm.trans h
  have hyZ₁ : ∀ z ∈ S.Z, y₁ * z * y₁⁻¹ ∈ S.Z := fun z hz => hZ.1 y₁ (by simp) z hz
  have hyZ₂ : ∀ z ∈ S.Z, y₂ * z * y₂⁻¹ ∈ S.Z := fun z hz => hZ.1 y₂ (by simp) z hz
  have hyB₁ : ∀ b ∈ S.B, y₁ * b * y₁⁻¹ ∈ S.B := he42sp_yB S hY.mem₁ hY.rho₁ hyZ₁
  have hyB₂ : ∀ b ∈ S.B, y₂ * b * y₂⁻¹ ∈ S.B := he42sp_yB2 S hyB₁ h0.1
  have hKZ : ∀ k ∈ S.K, ∀ z ∈ S.Z, k * z * k⁻¹ ∈ S.Z :=
    fun k hk z hz => S.hD.mem_Z_conj (hB.K_le_N hk) hz
  have hLB₁ : ∀ l ∈ S.L1, ∀ b ∈ S.B, l * b = b * l :=
    fun l hl b hb => (mem_centralizer_iff.mp (hB.L1_le_centralizer hl) b hb).symm
  have hLB₂ : ∀ l ∈ S.L2, ∀ b ∈ S.B, l * b = b * l :=
    fun l hl b hb => (mem_centralizer_iff.mp (hB.L2_le_centralizer hl) b hb).symm
  unfold HeSetup.StepSpread
  refine ⟨?_, ?_⟩
  · exact he42sp_side hPD₁ hB.A'_le_J hB.B_le_Z hB.card_B hB.card_Z hB.Z_le_A hB.Z_le_A'
      hB.A_comm hB.A'_comm hB.A_sq hLB₁ hn.1.1 hc.1 hy3₁ hyZ₁ hyB₁ hZ.2.1 hKZ
      inf_le_left hR.1.1 hR.1.2 h0.1 hZ.2.2.2
  · exact he42sp_side hPD₂ hB.A_le_J hB.B_le_Z hB.card_B hB.card_Z hB.Z_le_A' hB.Z_le_A
      hB.A'_comm hB.A_comm hB.A'_sq hLB₂ hn.2.1 hc.2 hy3₂ hyZ₂ hyB₂ hZ.2.2.1 hKZ
      inf_le_left hR.2.1.1 hR.2.1.2 h0.1 hZ.2.2.2

end CFSG.Quasithin.A94.He42
