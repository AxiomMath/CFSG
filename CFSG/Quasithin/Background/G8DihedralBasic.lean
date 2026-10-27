module

public import CFSG.Quasithin.Background.G8Complement
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

structure IsDihedralFamily {ι : Type*} (Hs : ι → Subgroup G) (p : ι → ℕ) : Prop where
  prime : ∀ i, (p i).Prime
  odd : ∀ i, Odd (p i)
  iso : ∀ i, Nonempty (↥(Hs i) ≃* DihedralGroup (p i))
  commute : ∀ i j, i ≠ j → ∀ x ∈ Hs i, ∀ y ∈ Hs j, x * y = y * x
  independent : iSupIndep Hs

namespace G8

structure DFam {ι : Type*} (Hs : ι → Subgroup G) (p : ι → ℕ) : Prop
    extends IsDihedralFamily Hs p where
  center : ∀ t ∈ ⨆ i, Hs i, (∀ s ∈ ⨆ i, Hs i, s * t = t * s) → t = 1

theorem exists_inverted_prime [Finite G] {a : G} (ha2 : a ^ 2 = 1) {Z : Subgroup G}
    (hZodd : Odd (Nat.card Z)) (hZa : ∀ z ∈ Z, a * z * a⁻¹ ∈ Z)
    (hnt : ∃ z ∈ Z, a * z * a⁻¹ ≠ z) :
    ∃ h ∈ Z, (orderOf h).Prime ∧ a * h * a⁻¹ = h⁻¹ := by
  obtain ⟨z, hz, hne⟩ := hnt
  set c := a * z * a⁻¹ with hc
  set y := z⁻¹ * c with hy
  have hcZ : c ∈ Z := hZa z hz
  have hyZ : y ∈ Z := Z.mul_mem (Z.inv_mem hz) hcZ
  have hy1 : y ≠ 1 := by
    intro h
    apply hne
    have : z⁻¹ * c = 1 := h
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hac : a * c * a⁻¹ = z := by
    have : a * c * a⁻¹ = (a * a) * z * (a * a)⁻¹ := by rw [hc]; group
    rw [this, ← pow_two, ha2]
    simp
  have hainv : a * y * a⁻¹ = y⁻¹ := by
    calc a * y * a⁻¹ = (a * z⁻¹ * a⁻¹) * (a * c * a⁻¹) := by rw [hy]; group
      _ = (a * z⁻¹ * a⁻¹) * z := by rw [hac]
      _ = y⁻¹ := by rw [hy, hc]; group
  have hodd : Odd (orderOf y) := hZodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Z hyZ)
  have hne1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne1
  have hpos : 0 < orderOf y := orderOf_pos y
  set k := orderOf y / p with hk
  have hk0 : k ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hpos hpd) hp.pos).ne'
  have hkd : k ∣ orderOf y := Nat.div_dvd_of_dvd hpd
  have hord : orderOf (y ^ k) = p := by
    rw [orderOf_pow_of_dvd hk0 hkd, hk, Nat.div_div_self hpd hpos.ne']
  refine ⟨y ^ k, Z.pow_mem hyZ k, hord ▸ hp, ?_⟩
  rw [← conj_pow, hainv, inv_pow]

theorem dihedral_equiv_of_inverting [Finite G] {a h : G} {p : ℕ} (hh : orderOf h = p)
    (ha2 : a ^ 2 = 1) (hinv : a * h * a⁻¹ = h⁻¹) (hane : a ∉ Subgroup.zpowers h) :
    Nonempty (↥(Subgroup.zpowers h ⊔ Subgroup.zpowers a) ≃* DihedralGroup p) := by
  set S := Subgroup.zpowers h ⊔ Subgroup.zpowers a with hS
  have hhS : h ∈ S := (le_sup_left : Subgroup.zpowers h ≤ S) (Subgroup.mem_zpowers h)
  have haS : a ∈ S := (le_sup_right : Subgroup.zpowers a ≤ S) (Subgroup.mem_zpowers a)
  set ρ : S := ⟨h, hhS⟩ with hρ
  set σ : S := ⟨a, haS⟩ with hσ
  have hgen : (⊤ : Subgroup S) = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    simp [hρ, hσ, hS]
  have hσ2 : σ ^ 2 = 1 := Subtype.ext (by simpa using ha2)
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (by simpa using hinv)
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro hmem
    apply hane
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have hρo : orderOf ρ = p := by rw [← hh, hρ, Subgroup.orderOf_mk]
  rw [hρo] at e
  exact ⟨e⟩

theorem eq_one_of_central_dihedral {K : Subgroup G} {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (e : ↥K ≃* DihedralGroup p) {t : G} (ht : t ∈ K) (hcomm : ∀ s ∈ K, s * t = t * s) :
    t = 1 := by
  have hc : e ⟨t, ht⟩ ∈ Subgroup.center (DihedralGroup p) := by
    rw [Subgroup.mem_center_iff]
    intro d
    obtain ⟨s, rfl⟩ := e.surjective d
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm s.1 s.2)
  rw [DihedralGroup.center_eq_bot_of_odd_ne_one hodd hp.ne_one, Subgroup.mem_bot] at hc
  have : (⟨t, ht⟩ : K) = 1 := e.injective (by rw [hc, map_one])
  exact congrArg Subtype.val this

theorem iSup_commute {ι₁ ι₂ : Type*} {H₁ : ι₁ → Subgroup G} {H₂ : ι₂ → Subgroup G}
    (h : ∀ i j, ∀ x ∈ H₁ i, ∀ y ∈ H₂ j, x * y = y * x) :
    ∀ x ∈ ⨆ i, H₁ i, ∀ y ∈ ⨆ j, H₂ j, x * y = y * x := by
  have h1 : ∀ i, H₁ i ≤ Subgroup.centralizer ((⨆ j, H₂ j : Subgroup G) : Set G) := by
    intro i x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have : (⨆ j, H₂ j) ≤ Subgroup.centralizer ({x} : Set G) := by
      refine iSup_le fun j y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h i j x hx y hy).symm
    have := this hy
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  intro x hx y hy
  have := (iSup_le h1 : (⨆ i, H₁ i) ≤ _) hx
  exact (Subgroup.mem_centralizer_iff.mp this) y hy |>.symm

theorem disjoint_sup_of_commute {K M J₁ J₂ : Subgroup G} (hKJ : K ≤ J₁) (hMJ : M ≤ J₁)
    (hcomm : ∀ m ∈ M, ∀ y ∈ J₂, m * y = y * m) (hKM : Disjoint K M) (hJ : Disjoint J₁ J₂) :
    Disjoint K (M ⊔ J₂) := by
  rw [Subgroup.disjoint_def] at hKM hJ ⊢
  intro x hxK hx
  obtain ⟨m, hm, y, hy, rfl⟩ := mem_sup_of_commute hcomm hx
  have hyJ₁ : y ∈ J₁ := by
    have := J₁.mul_mem (J₁.inv_mem (hMJ hm)) (hKJ hxK)
    simpa using this
  have hy1 : y = 1 := hJ hyJ₁ hy
  rw [hy1, mul_one] at hxK ⊢
  exact hKM hxK hm

namespace DFam

theorem single {K : Subgroup G} {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (e : ↥K ≃* DihedralGroup p) : DFam (fun _ : Unit => K) (fun _ => p) where
  prime _ := hp
  odd _ := hodd
  iso _ := ⟨e⟩
  commute i j hij := absurd (Subsingleton.elim i j) hij
  independent := iSupIndep_subsingleton _
  center t ht hc := by
    simp only [iSup_const] at ht hc
    exact eq_one_of_central_dihedral hp hodd e ht hc

theorem sumElim {ι₁ ι₂ : Type*} {H₁ : ι₁ → Subgroup G} {H₂ : ι₂ → Subgroup G}
    {p₁ : ι₁ → ℕ} {p₂ : ι₂ → ℕ} (h₁ : DFam H₁ p₁) (h₂ : DFam H₂ p₂)
    (hcomm : ∀ i j, ∀ x ∈ H₁ i, ∀ y ∈ H₂ j, x * y = y * x)
    (hdis : Disjoint (⨆ i, H₁ i) (⨆ j, H₂ j)) :
    DFam (Sum.elim H₁ H₂) (Sum.elim p₁ p₂) := by
  have hjoin : (⨆ x, Sum.elim H₁ H₂ x) = (⨆ i, H₁ i) ⊔ ⨆ j, H₂ j := by
    rw [iSup_sum]; rfl
  have hJ : ∀ x ∈ ⨆ i, H₁ i, ∀ y ∈ ⨆ j, H₂ j, x * y = y * x := iSup_commute hcomm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro (i | j)
    exacts [h₁.prime i, h₂.prime j]
  · rintro (i | j)
    exacts [h₁.odd i, h₂.odd j]
  · rintro (i | j)
    exacts [h₁.iso i, h₂.iso j]
  · rintro (i | j) (i' | j') hne x hx y hy
    · exact h₁.commute i i' (fun h => hne (by rw [h])) x hx y hy
    · exact hcomm i j' x hx y hy
    · exact (hcomm i' j y hy x hx).symm
    · exact h₂.commute j j' (fun h => hne (by rw [h])) x hx y hy
  · rw [iSupIndep_def]
    rintro (i | j)
    · have hle : (⨆ x, ⨆ (_ : x ≠ Sum.inl i), Sum.elim H₁ H₂ x) ≤
          (⨆ j, ⨆ (_ : j ≠ i), H₁ j) ⊔ ⨆ j, H₂ j := by
        refine iSup₂_le fun x hx => ?_
        rcases x with j | j
        · exact le_sup_of_le_left (le_iSup₂ (f := fun j (_ : j ≠ i) => H₁ j) j
            (fun h => hx (by rw [h])))
        · exact le_sup_of_le_right (le_iSup (fun j => H₂ j) j)
      refine Disjoint.mono_right hle (disjoint_sup_of_commute (le_iSup H₁ i) ?_ ?_ ?_ hdis)
      · exact iSup₂_le fun j _ => le_iSup H₁ j
      · intro m hm y hy
        exact hJ m ((iSup₂_le fun j _ => le_iSup H₁ j : (⨆ j, ⨆ (_ : j ≠ i), H₁ j) ≤ _) hm) y hy
      · exact iSupIndep_def.mp h₁.independent i
    · have hle : (⨆ x, ⨆ (_ : x ≠ Sum.inr j), Sum.elim H₁ H₂ x) ≤
          (⨆ j', ⨆ (_ : j' ≠ j), H₂ j') ⊔ ⨆ i, H₁ i := by
        refine iSup₂_le fun x hx => ?_
        rcases x with i | j'
        · exact le_sup_of_le_right (le_iSup (fun i => H₁ i) i)
        · exact le_sup_of_le_left (le_iSup₂ (f := fun j' (_ : j' ≠ j) => H₂ j') j'
            (fun h => hx (by rw [h])))
      refine Disjoint.mono_right hle (disjoint_sup_of_commute (le_iSup H₂ j) ?_ ?_ ?_ hdis.symm)
      · exact iSup₂_le fun j' _ => le_iSup H₂ j'
      · intro m hm y hy
        exact (hJ y hy m ((iSup₂_le fun j' _ => le_iSup H₂ j' :
          (⨆ j', ⨆ (_ : j' ≠ j), H₂ j') ≤ _) hm)).symm
      · exact iSupIndep_def.mp h₂.independent j
  · intro t ht hc
    rw [hjoin] at ht hc
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup_of_commute hJ ht
    have hx1 : x = 1 := by
      refine h₁.center x hx fun s hs => ?_
      have h1 := hc s (Subgroup.mem_sup_left hs)
      have h2 := hJ s hs y hy
      have : s * x * y = x * s * y := by
        calc s * x * y = s * (x * y) := mul_assoc _ _ _
          _ = x * y * s := h1
          _ = x * (y * s) := mul_assoc _ _ _
          _ = x * (s * y) := by rw [h2]
          _ = x * s * y := (mul_assoc _ _ _).symm
      exact mul_right_cancel this
    have hy1 : y = 1 := by
      refine h₂.center y hy fun s hs => ?_
      have h1 := hc s (Subgroup.mem_sup_right hs)
      have h2 := hJ x hx s hs
      have : x * (s * y) = x * (y * s) := by
        calc x * (s * y) = (x * s) * y := (mul_assoc _ _ _).symm
          _ = (s * x) * y := by rw [h2]
          _ = s * (x * y) := mul_assoc _ _ _
          _ = x * y * s := h1
          _ = x * (y * s) := mul_assoc _ _ _
      exact mul_left_cancel this
    rw [hx1, hy1, one_mul]

theorem comp_equiv {ι ι' : Type*} {Hs : ι → Subgroup G} {p : ι → ℕ} (h : DFam Hs p)
    (e : ι' ≃ ι) : DFam (Hs ∘ e) (p ∘ e) where
  prime i := h.prime (e i)
  odd i := h.odd (e i)
  iso i := h.iso (e i)
  commute i j hij := h.commute (e i) (e j) (fun h' => hij (e.injective h'))
  independent := h.independent.comp e.injective
  center t ht hc := by
    have hj : (⨆ i', (Hs ∘ e) i') = ⨆ i, Hs i := Equiv.iSup_comp (g := Hs) e
    rw [hj] at ht hc
    exact h.center t ht hc

end DFam

end G8

end CFSG.Quasithin
