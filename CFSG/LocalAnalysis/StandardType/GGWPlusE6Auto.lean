module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelData
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModule

public section

namespace CFSG.StandardType

open CFSG CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

private noncomputable def GGE6AutoAdActFin (u : WeylGroup .E6) (x : Fin 6 → ZMod 3) :
    Fin 6 → ZMod 3 :=
  TableBExc.E6Three.adAct .E6 3 u x

private theorem GGE6AutoAdActFin_one (x : Fin 6 → ZMod 3) :
    GGE6AutoAdActFin 1 x = x :=
  TableBExc.E6Three.adAct_one (τ := Tag.E6) (p := 3) x

private theorem GGE6AutoAdActFin_mul (u v : WeylGroup .E6) (x : Fin 6 → ZMod 3) :
    GGE6AutoAdActFin (u * v) x = GGE6AutoAdActFin u (GGE6AutoAdActFin v x) :=
  TableBExc.E6Three.adAct_mul u v x

private theorem GGE6AutoAdActFin_simple (i : Fin Tag.E6.rank) (x : Fin 6 → ZMod 3) :
    GGE6AutoAdActFin (simple .E6 i) x = TableBExc.E6Three.adRefl .E6 3 i x :=
  TableBExc.E6Three.adAct_simple i x

private noncomputable def GGE6AutoGood {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (Φ : A →* Multiplicative (Fin 6 → ZMod 3)) (x : MulAut L') (u : WeylGroup .E6) : Prop :=
  ∀ a b : A, (b : MulAut L') = x * a * x⁻¹ →
    Multiplicative.toAdd (Φ b) =
      GGE6AutoAdActFin u (Multiplicative.toAdd (Φ a))

theorem GGE6ThreeData.exists_automizer_hom
    {L' : Type} [Group L'] [Finite L'] {Z : Subgroup L'} {A : Subgroup (MulAut L')}
    {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'} {w : Fin 6 → L'}
    (h : GGE6ThreeData Z A Φ T w) :
    ∃ ρ : ↥((MulAut.conj : L' →* MulAut L').range ⊓ Subgroup.normalizer (A : Set (MulAut L'))) →*
        WeylGroup .E6,
      Function.Surjective ρ ∧
        ρ.ker ≤ (Subgroup.centralizer (A : Set (MulAut L'))).subgroupOf
          ((MulAut.conj : L' →* MulAut L').range ⊓ Subgroup.normalizer (A : Set (MulAut L'))) := by
  classical
  let N : Subgroup (MulAut L') := Subgroup.normalizer (A : Set (MulAut L'))
  let X : Subgroup (MulAut L') := (MulAut.conj : L' →* MulAut L').range ⊓ N
  let C : Subgroup (MulAut L') := Subgroup.centralizer (A : Set (MulAut L'))
  have huniq : ∀ {x : MulAut L'} {u u' : WeylGroup .E6}, x ∈ N →
      GGE6AutoGood Φ x u → GGE6AutoGood Φ x u' → u = u' := by
    intro x u u' hx hu hu'
    have key : ∀ a : A,
        GGE6AutoAdActFin u (Multiplicative.toAdd (Φ a)) =
          GGE6AutoAdActFin u' (Multiplicative.toAdd (Φ a)) := by
      intro a
      have hmem : x * (a : MulAut L') * x⁻¹ ∈ A :=
        (Subgroup.mem_set_normalizer_iff.mp hx (a : MulAut L')).mp a.2
      let b : A := ⟨x * (a : MulAut L') * x⁻¹, hmem⟩
      have hb : (b : MulAut L') = x * a * x⁻¹ := rfl
      exact (hu a b hb).symm.trans (hu' a b hb)
    rcases h.range with hr | hr
    ·
      have hpoint : ∀ v : Fin 6 → ZMod 3,
          TableBExc.E6Three.adAct .E6 3 u v = TableBExc.E6Three.adAct .E6 3 u' v := by
        intro v
        have hv : Multiplicative.ofAdd v ∈ Φ.range := by
          rw [hr]; exact Subgroup.mem_top _
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hv
        have ht : Multiplicative.toAdd (Φ a) = v := congrArg Multiplicative.toAdd ha
        have h := key a
        rw [ht] at h
        exact h
      have hperm : TableBExc.E6Three.adPerm .E6 3 u =
          TableBExc.E6Three.adPerm .E6 3 u' := by
        apply Equiv.ext
        intro v
        exact hpoint v
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact NoOffRest.adPerm_injective (τ := Tag.E6) (p := 3) (by norm_num) hperm
    ·
      have hpoint : ∀ v : Fin 6 → ZMod 3, v ∈ NoOffRest.hypE6 →
          TableBExc.E6Three.adAct .E6 3 u v = TableBExc.E6Three.adAct .E6 3 u' v := by
        intro v hv
        have hv' : Multiplicative.ofAdd v ∈ Φ.range := (hr v).mpr hv
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hv'
        have ht : Multiplicative.toAdd (Φ a) = v := congrArg Multiplicative.toAdd ha
        have h := key a
        rw [ht] at h
        exact h
      have hfix : ∀ v ∈ NoOffRest.hypE6,
          TableBExc.E6Three.adAct .E6 3 (u'⁻¹ * u) v = v := by
        intro v hv
        have hkey : TableBExc.E6Three.adAct .E6 3 u v =
            TableBExc.E6Three.adAct .E6 3 u' v := hpoint v hv
        calc TableBExc.E6Three.adAct .E6 3 (u'⁻¹ * u) v
            = TableBExc.E6Three.adAct .E6 3 u'⁻¹
                (TableBExc.E6Three.adAct .E6 3 u v) :=
              TableBExc.E6Three.adAct_mul u'⁻¹ u v
          _ = TableBExc.E6Three.adAct .E6 3 u'⁻¹
                (TableBExc.E6Three.adAct .E6 3 u' v) := by rw [hkey]
          _ = TableBExc.E6Three.adAct .E6 3 (u'⁻¹ * u') v :=
              (TableBExc.E6Three.adAct_mul u'⁻¹ u' v).symm
          _ = TableBExc.E6Three.adAct .E6 3 1 v := by rw [inv_mul_cancel]
          _ = v := TableBExc.E6Three.adAct_one v
      have h1 : u'⁻¹ * u = 1 := TableBExc.E6Three.eq_one_of_adAct_eq_on_hypE6 hfix
      exact (inv_mul_eq_one.mp h1).symm
  have hex : ∀ x : X, ∃ u : WeylGroup .E6, GGE6AutoGood Φ (x : MulAut L') u := by
    intro x
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp (Subgroup.mem_inf.mp x.2).1
    have hnN : MulAut.conj n ∈ N := by
      rw [hn]; exact (Subgroup.mem_inf.mp x.2).2
    obtain ⟨u, hu⟩ := h.inner n hnN
    refine ⟨u, ?_⟩
    intro a b hb
    exact hu a b (by rw [hb, hn])
  let uOf : X → WeylGroup .E6 := fun x => Classical.choose (hex x)
  have hρspec : ∀ x : X, GGE6AutoGood Φ (x : MulAut L') (uOf x) :=
    fun x => Classical.choose_spec (hex x)
  have hρone : uOf 1 = 1 := by
    refine huniq (x := (1 : MulAut L')) (u := uOf 1) (u' := 1) (Subgroup.one_mem N)
      (hρspec 1) ?_
    intro a b hb
    have hba : b = a := Subtype.ext (by simpa using hb)
    rw [hba]
    exact (GGE6AutoAdActFin_one (Multiplicative.toAdd (Φ a))).symm
  have hρmul : ∀ x y : X, uOf (x * y) = uOf x * uOf y := by
    intro x y
    refine huniq (x := ((x * y : X) : MulAut L')) (u := uOf (x * y))
      (u' := uOf x * uOf y) ((Subgroup.mem_inf.mp (x * y).2).2) (hρspec (x * y)) ?_
    intro a b hb
    have hb0 : (b : MulAut L') =
        (x : MulAut L') * (y : MulAut L') * (a : MulAut L') *
          ((x : MulAut L') * (y : MulAut L'))⁻¹ := by
      simpa only [Subgroup.coe_mul] using hb
    have hcA : (y : MulAut L') * (a : MulAut L') * (y : MulAut L')⁻¹ ∈ A :=
      (Subgroup.mem_set_normalizer_iff.mp (Subgroup.mem_inf.mp y.2).2 (a : MulAut L')).mp a.2
    let c : A := ⟨(y : MulAut L') * (a : MulAut L') * (y : MulAut L')⁻¹, hcA⟩
    have hc : (c : MulAut L') =
        (y : MulAut L') * (a : MulAut L') * (y : MulAut L')⁻¹ := rfl
    have hb'' : (b : MulAut L') =
        (x : MulAut L') * (c : MulAut L') * (x : MulAut L')⁻¹ := by
      rw [hc, hb0]; group
    rw [GGE6AutoAdActFin_mul, ← hρspec y a c hc]
    exact hρspec x c b hb''
  let ρ : X →* WeylGroup .E6 :=
    { toFun := uOf
      map_one' := hρone
      map_mul' := hρmul }
  have hρspec' : ∀ x : X, GGE6AutoGood Φ (x : MulAut L') (ρ x) := fun x => hρspec x
  have hconjX : ∀ i : Fin Tag.E6.rank, MulAut.conj (w i) ∈ X := by
    intro i
    refine Subgroup.mem_inf.mpr ⟨MonoidHom.mem_range.mpr ⟨w i, rfl⟩, ?_⟩
    exact mem_normalizer_of_conj_mem (fun a ha => by
      obtain ⟨b, hbconj, _⟩ := h.act i ⟨a, ha⟩
      rw [hbconj]
      exact b.2)
  have hconjGood : ∀ i : Fin Tag.E6.rank,
      GGE6AutoGood Φ (MulAut.conj (w i)) (simple .E6 i) := by
    intro i a b hb
    obtain ⟨b', hb', hb'Φ⟩ := h.act i a
    have hbb' : b = b' := Subtype.ext (hb.trans hb')
    rw [hbb', GGE6AutoAdActFin_simple]
    exact hb'Φ
  have hsimple : ∀ i : Fin Tag.E6.rank,
      ρ ⟨MulAut.conj (w i), hconjX i⟩ = simple .E6 i := by
    intro i
    refine huniq (x := MulAut.conj (w i)) (u := ρ ⟨MulAut.conj (w i), hconjX i⟩)
      (u' := simple .E6 i) ((Subgroup.mem_inf.mp (hconjX i)).2) ?_ (hconjGood i)
    exact hρspec' ⟨MulAut.conj (w i), hconjX i⟩
  have hsurj : Function.Surjective ρ := by
    intro u
    refine TableBExc.E6Three.weyl_induction (fun u => ∃ n : X, ρ n = u)
      ⟨1, map_one ρ⟩ ?_ u
    intro i w' hw'
    obtain ⟨n, hn⟩ := hw'
    exact ⟨⟨MulAut.conj (w i), hconjX i⟩ * n, by rw [map_mul, hsimple i, hn]⟩
  have hker : ρ.ker ≤ C.subgroupOf X := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro a ha
    have hx1 : ρ x = 1 := MonoidHom.mem_ker.mp hx
    let aA : A := ⟨a, ha⟩
    have hbA : (x : MulAut L') * (aA : MulAut L') * (x : MulAut L')⁻¹ ∈ A :=
      (Subgroup.mem_set_normalizer_iff.mp (Subgroup.mem_inf.mp x.2).2 (aA : MulAut L')).mp aA.2
    let b : A := ⟨(x : MulAut L') * (aA : MulAut L') * (x : MulAut L')⁻¹, hbA⟩
    have hb : (b : MulAut L') =
        (x : MulAut L') * (aA : MulAut L') * (x : MulAut L')⁻¹ := rfl
    have hgood := hρspec' x aA b hb
    have hΦeq : Multiplicative.toAdd (Φ b) = Multiplicative.toAdd (Φ aA) := by
      rw [hgood, hx1, GGE6AutoAdActFin_one]
    have hba : b = aA := h.injective (by simpa using congrArg Multiplicative.ofAdd hΦeq)
    have hconj : (x : MulAut L') * (aA : MulAut L') * (x : MulAut L')⁻¹ = aA := by
      have := congrArg (fun y : A => (y : MulAut L')) hba
      simpa [hb] using this
    have : (aA : MulAut L') * (x : MulAut L') = (x : MulAut L') * (aA : MulAut L') := by
      calc (aA : MulAut L') * (x : MulAut L')
          = ((x : MulAut L') * (aA : MulAut L') * (x : MulAut L')⁻¹) *
              (x : MulAut L') := by simp only [hconj]
        _ = (x : MulAut L') * (aA : MulAut L') := by group
    exact this
  exact ⟨ρ, hsurj, hker⟩

end CFSG.StandardType
