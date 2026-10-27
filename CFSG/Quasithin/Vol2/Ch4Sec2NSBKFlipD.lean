module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKFlipC
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Irr
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

theorem comm_centralizes_nsbkfd {G : Type} [Group G] {V : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (hy : y ∈ Subgroup.normalizer (V : Set G))
    (h : ∀ t ∈ V, (x * y) * t * (x * y)⁻¹ = (y * x) * t * (y * x)⁻¹) :
    ⁅x, y⁆ ∈ Subgroup.centralizer (V : Set G) := by
  have hyx : y * x ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ hy hx
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have ht₁ : (y * x)⁻¹ * t * (y * x) ∈ V := by
    have := (Subgroup.mem_normalizer_iff''.mp hyx t).mp ht
    simpa using this
  have h1 := h _ ht₁
  have h2 : (y * x) * ((y * x)⁻¹ * t * (y * x)) * (y * x)⁻¹ = t := by group
  rw [h2] at h1
  have hcm : ⁅x, y⁆ = (x * y) * (y * x)⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hct : ((x * y) * (y * x)⁻¹) * t * ((x * y) * (y * x)⁻¹)⁻¹ = t := by
    calc ((x * y) * (y * x)⁻¹) * t * ((x * y) * (y * x)⁻¹)⁻¹
        = (x * y) * ((y * x)⁻¹ * t * (y * x)) * (x * y)⁻¹ := by group
      _ = t := h1
  rw [hcm]
  exact (mul_inv_eq_iff_eq_mul.mp hct).symm

section Succ

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k j : ℕ}

theorem ainv_of_normalizes (D : StdData G T L I K m k (m + 1) j)
    (hKU : ∀ x : ↥K, ∀ z ∈ uZero I K, (x : G) * z * (x : G)⁻¹ ∈ uZero I K) {l : ↥K}
    (hl : ∀ v ∈ vV T L, (l : G) * v * (l : G)⁻¹ ∈ vV T L) : AInv D l := by
  intro a ha
  obtain ⟨v, hvV, i, hvi⟩ := D.cover a (fun b hb => by
    have hb' : b = Fin.last m := by
      apply Fin.ext
      have := b.2
      simp only [Fin.val_last]
      omega
    rw [hb']
    exact ha)
  set v' : ↥(uZero I K) := ⟨(l : G) * v * (l : G)⁻¹, hKU l v v.2⟩ with hv'
  have hv'V : (v' : G) ∈ vV T L := hl v hvV
  have h := D.equi l v v' rfl i
  have h0 := D.vcoord v' hv'V i (Fin.last m) (by simp)
  rw [h, hvi] at h0
  exact h0

theorem mem_vV_iff_wSub (D : StdData G T L I K m k (m + 1) j) (hVU : vV T L ≤ uZero I K)
    (hjk : j = k) {t : G} : t ∈ vV T L ↔ t ∈ wSub D := by
  constructor
  · intro ht
    refine ⟨hVU ht, ?_⟩
    funext i
    have h := D.vcoord ⟨t, hVU ht⟩ ht i (Fin.last m) (by simp)
    rw [← coG_of_mem D ⟨t, hVU ht⟩] at h
    exact h
  · rintro ⟨htU, hw⟩
    refine D.veq hjk ⟨t, htU⟩ (fun i b hb => ?_)
    have hb' : b = Fin.last m := by
      apply Fin.ext
      have := b.2
      simp only [Fin.val_last]
      omega
    rw [hb', ← coG_of_mem D ⟨t, htU⟩]
    exact congrFun hw i

theorem flip_conclusion_succ (hc : Conf4212 G T M L I H K) (h22 : ASC22Three G) (hIH : I ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hVU : vV T L ≤ uZero I K) (hj : 0 < j)
    (hjm : j = m) (hkm : k = m) (D : StdData G T L I K m k (m + 1) j)
    (hRlt : pCoreOf 2 I < rPlus T M L) (hRC : rPlus T M L ≤ Subgroup.centralizer (vV T L : Set G))
    {g : G} (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I)
    (h3 : ∃ u ∈ uZero I K, g⁻¹ * u * g ∉ kerA (K ⊔ pCoreOf 2 I) (gammaZero T M L I)) :
    (∀ v ∈ vV T L, g * v * g⁻¹ ∈ vV T L) ∧
      (∀ l ∈ L, ∀ l' ∈ L, ⁅g * l' * g⁻¹, l⁆ ∈ Subgroup.centralizer (vV T L : Set G)) := by
  have hjk : j = k := by omega
  have hRCV : pCoreOf 2 I ≤ Subgroup.centralizer (vV T L : Set G) :=
    fun r hr => hRC (hRlt.le hr)
  have hRΓ : pCoreOf 2 I ≤ gammaZero T M L I := fun r hr =>
    ⟨⟨(hRlt.le hr).2, Subgroup.le_normalizer hr⟩, hRC (hRlt.le hr)⟩
  have hnormU : K ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (uZero I K : Set G) :=
    le_normalizer_uZero hIH hHK
  have hKU : ∀ x : ↥K, ∀ z ∈ uZero I K, (x : G) * z * (x : G)⁻¹ ∈ uZero I K := fun x z hz =>
    (Subgroup.mem_normalizer_iff.mp (hnormU (Subgroup.mem_sup_left x.2)) z).mp hz
  have F : RForm D := rForm_of hIH hHK hj D hRCV
  have hA := exists_arOf_ne_zero h22 hc hIH hHK hj D F hRΓ h1 h3
  have hA' := exists_arOf_ne_zero' hj D F h1 h2 hA
  obtain ⟨ab, ab', hab, hab'⟩ := exists_flip_equivs hj F hjm h1 h2 hA hA'
  let E : FlipEq D hj g := ⟨ab, ab', hab, hab'⟩
  have hG1 : ∀ v ∈ vV T L, g * v * g⁻¹ ∈ vV T L := fun v hv =>
    (mem_vV_iff_wSub D hVU hjk).mpr (flip_maps_V F h1 h2 E ((mem_vV_iff_wSub D hVU hjk).mp hv))
  refine ⟨hG1, ?_⟩
  intro l hl l' hl'
  obtain ⟨a, haLH, ha⟩ := hc.exists_act_L hl
  obtain ⟨a', ha'LH, ha'⟩ := hc.exists_act_L hl'
  have hgN : g ∈ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) :=
    A4.mem_normalizer_of_conj_mem hG1
  have hgN' : g⁻¹ ∈ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) := Subgroup.inv_mem _ hgN
  have haN : a ∈ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) := hc.LH_le_normalizer_V haLH
  have ha'N : a' ∈ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) :=
    hc.LH_le_normalizer_V ha'LH
  have hconjV : ∀ {x : G}, x ∈ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) →
      ∀ t ∈ vV T L, x * t * x⁻¹ ∈ vV T L := fun {x} hx t ht =>
    (Subgroup.mem_normalizer_iff.mp hx t).mp ht
  have hx : ∀ t ∈ vV T L, g * l' * g⁻¹ * t * (g * l' * g⁻¹)⁻¹ =
      (g * a' * g⁻¹) * t * (g * a' * g⁻¹)⁻¹ := by
    intro t ht
    have htg : g⁻¹ * t * g⁻¹⁻¹ ∈ vV T L := hconjV hgN' t ht
    have h := ha' _ (by simpa using htg)
    calc g * l' * g⁻¹ * t * (g * l' * g⁻¹)⁻¹ = g * (l' * (g⁻¹ * t * g) * l'⁻¹) * g⁻¹ := by group
      _ = g * (a' * (g⁻¹ * t * g) * a'⁻¹) * g⁻¹ := by rw [h]
      _ = (g * a' * g⁻¹) * t * (g * a' * g⁻¹)⁻¹ := by group
  have hx₀N : g * a' * g⁻¹ ∈ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN ha'N) hgN'
  have hxN : g * l' * g⁻¹ ∈ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) :=
    A4.mem_normalizer_of_conj_mem (fun t ht => by rw [hx t ht]; exact hconjV hx₀N t ht)
  have hyN : l ∈ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) :=
    A4.mem_normalizer_of_conj_mem (fun t ht => by rw [ha t ht]; exact hconjV haN t ht)
  have hLK : perfectCore (L ⊓ H) ≤ K := hc.LH_le
  have hainv : AInv D ⟨a, hLK haLH⟩ :=
    ainv_of_normalizes D hKU (fun v hv => hconjV haN v hv)
  have hainv' : AInv D ⟨a', hLK ha'LH⟩ :=
    ainv_of_normalizes D hKU (fun v hv => hconjV ha'N v hv)
  refine comm_centralizes_nsbkfd hxN hyN (fun t ht => ?_)
  have hfc := flip_commutes F h1 h2 E hKU hainv hainv'
    ((mem_vV_iff_wSub D hVU hjk).mp ht)
  have hat : a * t * a⁻¹ ∈ vV T L := hconjV haN t ht
  have hx₀t : (g * a' * g⁻¹) * t * (g * a' * g⁻¹)⁻¹ ∈ vV T L := hconjV hx₀N t ht
  calc g * l' * g⁻¹ * l * t * (g * l' * g⁻¹ * l)⁻¹
      = g * l' * g⁻¹ * (l * t * l⁻¹) * (g * l' * g⁻¹)⁻¹ := by group
    _ = g * l' * g⁻¹ * (a * t * a⁻¹) * (g * l' * g⁻¹)⁻¹ := by rw [ha t ht]
    _ = (g * a' * g⁻¹) * (a * t * a⁻¹) * (g * a' * g⁻¹)⁻¹ := hx _ hat
    _ = (g * a' * g⁻¹ * a) * t * (g * a' * g⁻¹ * a)⁻¹ := by group
    _ = (a * (g * a' * g⁻¹)) * t * (a * (g * a' * g⁻¹))⁻¹ := hfc
    _ = a * ((g * a' * g⁻¹) * t * (g * a' * g⁻¹)⁻¹) * a⁻¹ := by group
    _ = l * ((g * a' * g⁻¹) * t * (g * a' * g⁻¹)⁻¹) * l⁻¹ := (ha _ hx₀t).symm
    _ = l * (g * l' * g⁻¹ * t * (g * l' * g⁻¹)⁻¹) * l⁻¹ := by rw [hx t ht]
    _ = (l * (g * l' * g⁻¹)) * t * (l * (g * l' * g⁻¹))⁻¹ := by group

end Succ

end CFSG.Quasithin.H13.Ch4.NSB
