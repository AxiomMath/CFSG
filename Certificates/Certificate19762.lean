module

public import CFSG.Sporadic.Schreier.M11Data
public meta import CFSG.Sporadic.Schreier.M11Data
import CFSG.Certificates.Kernel.PermCent.SmallBSound
import Certificates.Kernel.PermCent.K19762
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV

namespace Certificates

open CertificateChecks

private theorem product_map_ev19762 {α β : Type*} (f : α → β) (l₁ l₂ : List α) :
    l₁.map f ×ˢ l₂.map f = (l₁ ×ˢ l₂).map (Prod.map f f) := by
  simp [SProd.sprod, List.product, List.flatMap_map, List.map_flatMap, List.map_map,
    Function.comp_def]

private theorem word19762_eq :
    orderIs (m11gA * m11gB * m11gA * m11gB⁻¹ * m11gA * m11gB * m11gB) 5 = M11B.wordC := by
  rw [eq_ev_cOf m11gA, eq_ev_cOf m11gB, M11B.wordC.eq_1, M11B.A.eq_1, M11B.B.eq_1]
  simp only [ev_mul', ev_inv', orderIs_ev]
  exact orderIs_eq_P _ 5 [5] (by norm_num) (by decide) (by decide)

private theorem count19762_eq :
    ((m11Elements.filter (orderIs · 2) ×ˢ m11Elements.filter (orderIs · 4)).filter
      fun q => orderIs (q.1 * q.2) 11 && orderIs (q.1 * q.2 * q.1⁻¹ * q.2⁻¹) 6 &&
        orderIs (q.1 * q.2 * q.1 * q.2⁻¹ * q.1 * q.2 * q.2) 5).length = M11B.pairCntC := by
  have o2 : ∀ g : CV 11, orderIs g 2 = orderIsP g 2 [2] :=
    fun g => orderIs_eq_P g 2 [2] (by norm_num) (by decide) (by decide)
  have o4 : ∀ g : CV 11, orderIs g 4 = orderIsP g 4 [2] :=
    fun g => orderIs_eq_P g 4 [2] (by norm_num) (by decide) (by decide)
  have o5 : ∀ g : CV 11, orderIs g 5 = orderIsP g 5 [5] :=
    fun g => orderIs_eq_P g 5 [5] (by norm_num) (by decide) (by decide)
  have o6 : ∀ g : CV 11, orderIs g 6 = orderIsP g 6 [2, 3] :=
    fun g => orderIs_eq_P g 6 [2, 3] (by norm_num) (by decide) (by decide)
  have o11 : ∀ g : CV 11, orderIs g 11 = orderIsP g 11 [11] :=
    fun g => orderIs_eq_P g 11 [11] (by norm_num) (by decide) (by decide)
  have hE : m11Elements = (elemsC m11Certificate).map ev := elemsT_eq_elemsC m11Certificate
  rw [M11B.pairCntC.eq_1, M11B.E.eq_1, hE, List.filter_map, List.filter_map, product_map_ev19762,
    List.filter_map, List.length_map]
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, ev_mul', ev_inv', orderIs_ev, o2, o4,
    o5, o6, o11]

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu in
theorem certificate19762 : orderIs (m11gA * m11gB * m11gA * m11gB⁻¹ * m11gA * m11gB * m11gB) 5 = true ∧
    ((m11Elements.filter (orderIs · 2) ×ˢ m11Elements.filter (orderIs · 4)).filter
      fun q => orderIs (q.1 * q.2) 11 && orderIs (q.1 * q.2 * q.1⁻¹ * q.2⁻¹) 6 &&
        orderIs (q.1 * q.2 * q.1 * q.2⁻¹ * q.1 * q.2 * q.2) 5).length = 7920 := by
  rw [word19762_eq, count19762_eq]
  exact ⟨KernelPermCent.k19762_word, KernelPermCent.k19762_count⟩

end Certificates
