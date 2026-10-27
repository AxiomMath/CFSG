module

public import CFSG.Quasithin.Recognition.J2RecCzIso
public import CFSG.Quasithin.Recognition.St84.SemidirectRec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv CFSG.LieType.BorelTits

namespace J2Cz

open QM

theorem linePerm_conj (p : QM) : linePerm (MulAut.conj p) = 1 :=
  Equiv.ext fun j => (linePerm_eq (conj_x p j)).trans (Perm.one_apply j).symm

theorem eq_one_of_conj_mem_L0 {p : QM} (hp : MulAut.conj p ∈ L0) : MulAut.conj p = 1 := by
  refine aut_ext fun j => ?_
  rw [hp j.succ, linePerm_conj, Perm.one_apply, MulAut.one_apply]

noncomputable def lineHom : ↥L0 →* alternatingGroup (Fin 5) where
  toFun α := ⟨linePerm α, linePerm_mem_alternatingGroup α.2⟩
  map_one' := Subtype.ext (map_one linePermHom)
  map_mul' α β := Subtype.ext (map_mul linePermHom (α : MulAut QM) β)

theorem lineHom_injective : Function.Injective lineHom := by
  intro α β hαβ
  have h' : linePerm (α : MulAut QM) = linePerm β := congrArg Subtype.val hαβ
  refine Subtype.ext (aut_ext fun j => ?_)
  rw [α.2, β.2, h']

theorem lineHom_surjective : Function.Surjective lineHom := by
  set M := lineHom.range.map (alternatingGroup (Fin 5)).subtype with hM
  have hle : Subgroup.closure ({pa, pb} : Set (Perm (Fin 5))) ≤ M := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨⟨pa, pa_mem⟩, ⟨⟨phiA, phiA_mem⟩, Subtype.ext linePerm_phiA⟩, rfl⟩
    · exact ⟨⟨pb, pb_mem⟩, ⟨⟨phiB, phiB_mem⟩, Subtype.ext linePerm_phiB⟩, rfl⟩
  rw [closure_pa_pb] at hle
  intro σ
  obtain ⟨τ, ⟨α, hα⟩, hτσ⟩ := hle σ.2
  exact ⟨α, hα.trans (Subtype.ext hτσ)⟩

noncomputable def lineEquiv : ↥L0 ≃* alternatingGroup (Fin 5) :=
  MulEquiv.ofBijective lineHom ⟨lineHom_injective, lineHom_surjective⟩

theorem linePerm_lineEquiv_symm (σ : alternatingGroup (Fin 5)) :
    linePerm (lineEquiv.symm σ : MulAut QM) = σ :=
  congrArg Subtype.val (lineEquiv.apply_symm_apply σ)

theorem lineEquiv_symm_pa : (lineEquiv.symm ⟨pa, pa_mem⟩ : MulAut QM) = phiA := by
  have : lineEquiv ⟨phiA, phiA_mem⟩ = ⟨pa, pa_mem⟩ := Subtype.ext linePerm_phiA
  rw [← this, MulEquiv.symm_apply_apply]

end J2Cz

open J2Cz J2Cz.QM CFSG.Quasithin.F112R.St84

section General

variable {G : Type} [Group G]

noncomputable def czActOf {P : Subgroup G} (χ : ↥(pCoreOf 2 P) ≃* QM) : ↥P →* MulAut QM :=
  parAct (le_normalizer_pCoreOf 2 P) χ

@[expose]
noncomputable def symmZ {P : Subgroup G} (χ : ↥(pCoreOf 2 P) ≃* QM) : ↥P :=
  ⟨((χ.symm QM.z : ↥(pCoreOf 2 P)) : G), pCoreOf_le 2 P (χ.symm QM.z).2⟩

theorem czActOf_apply {P : Subgroup G} (χ : ↥(pCoreOf 2 P) ≃* QM) (h : ↥P) (p : QM) :
    ((χ.symm (czActOf χ h p) : ↥(pCoreOf 2 P)) : G) =
      (h : G) * χ.symm p * (h : G)⁻¹ := by
  rw [czActOf, parAct_apply, MulEquiv.symm_apply_apply]

theorem czActOf_of_mem {P : Subgroup G} (χ : ↥(pCoreOf 2 P) ≃* QM) {q : G}
    (hq : q ∈ pCoreOf 2 P) :
    czActOf χ ⟨q, pCoreOf_le 2 P hq⟩ = MulAut.conj (χ ⟨q, hq⟩) :=
  parAct_of_mem hq (pCoreOf_le 2 P hq)

theorem czActOf_symm_z {P : Subgroup G} (χ : ↥(pCoreOf 2 P) ≃* QM) :
    czActOf χ (symmZ χ) = 1 := by
  rw [symmZ, czActOf_of_mem χ (χ.symm QM.z).2]
  have hχ : χ ⟨((χ.symm QM.z : ↥(pCoreOf 2 P)) : G), (χ.symm QM.z).2⟩ = QM.z := by
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
  rw [hχ]
  refine MulEquiv.ext fun p => ?_
  rw [MulAut.conj_apply, MulAut.one_apply, QM.z_comm p]
  group

theorem symmZ_sq {P : Subgroup G} (χ : ↥(pCoreOf 2 P) ≃* QM) :
    symmZ χ * symmZ χ = 1 := by
  apply Subtype.ext
  have h : (χ.symm QM.z : ↥(pCoreOf 2 P)) * (χ.symm QM.z : ↥(pCoreOf 2 P)) = 1 := by
    apply χ.injective
    rw [map_mul, MulEquiv.apply_symm_apply, QM.z_sq, map_one]
  simpa [symmZ] using congrArg Subtype.val h

theorem symmZ_mem_center {P : Subgroup G} (χ : ↥(pCoreOf 2 P) ≃* QM) :
    symmZ χ ∈ Subgroup.center ↥P := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  set zQ : ↥(pCoreOf 2 P) := χ.symm QM.z with hzQ
  change (g : G) * (zQ : G) = (zQ : G) * (g : G)
  have hzQcomm : ∀ q : ↥(pCoreOf 2 P), zQ * q = q * zQ := by
    intro q
    apply χ.injective
    rw [map_mul, map_mul, hzQ, MulEquiv.apply_symm_apply]
    exact QM.z_comm (χ q)
  let c : G := (g : G) * (zQ : G) * (g : G)⁻¹
  have hgN : (g : G) ∈ Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G) :=
    le_normalizer_pCoreOf 2 P g.2
  have hcQ : c ∈ pCoreOf 2 P :=
    (Subgroup.mem_normalizer_iff.mp hgN (zQ : G)).mp zQ.2
  have hc_center : ∀ q : ↥(pCoreOf 2 P),
      (⟨c, hcQ⟩ : ↥(pCoreOf 2 P)) * q = q * ⟨c, hcQ⟩ := by
    intro q
    apply Subtype.ext
    change c * (q : G) = (q : G) * c
    have hq' : (g : G)⁻¹ * (q : G) * (g : G) ∈ pCoreOf 2 P := by
      have hgN' : (g : G)⁻¹ ∈ Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G) :=
        Subgroup.inv_mem _ hgN
      simpa using (Subgroup.mem_normalizer_iff.mp hgN' (q : G)).mp q.2
    have hzq' : (zQ : G) * ((g : G)⁻¹ * (q : G) * (g : G)) =
        ((g : G)⁻¹ * (q : G) * (g : G)) * (zQ : G) :=
      congrArg Subtype.val (hzQcomm ⟨_, hq'⟩)
    calc c * (q : G) =
          (g : G) * ((zQ : G) * ((g : G)⁻¹ * (q : G) * (g : G))) * (g : G)⁻¹ := by
          simp only [c]
          group
      _ = (g : G) * (((g : G)⁻¹ * (q : G) * (g : G)) * (zQ : G)) * (g : G)⁻¹ := by
            rw [hzq']
      _ = (q : G) * c := by
            simp only [c]
            group
  have hc_central : ∀ m : QM, χ ⟨c, hcQ⟩ * m = m * χ ⟨c, hcQ⟩ := by
    intro m
    let q : ↥(pCoreOf 2 P) := χ.symm m
    have h := hc_center q
    have h' : χ ⟨c, hcQ⟩ * χ q = χ q * χ ⟨c, hcQ⟩ := by
      have hq_eq : (⟨c, hcQ⟩ : ↥(pCoreOf 2 P)) * q = q * ⟨c, hcQ⟩ := h
      rw [← map_mul, ← map_mul, hq_eq]
    simpa [q] using h'
  rcases QM.eq_of_comm_x (χ ⟨c, hcQ⟩) (fun j => hc_central (QM.x j)) with h1 | h1
  · have hc1 : c = 1 := by
      have h2 : χ ⟨c, hcQ⟩ = χ (1 : ↥(pCoreOf 2 P)) := by rw [h1, map_one]
      exact congrArg Subtype.val (χ.injective h2)
    have hz1 : zQ = 1 := by
      apply Subtype.ext
      calc (zQ : G) = (g : G)⁻¹ * c * (g : G) := by
            simp only [c]
            group
        _ = 1 := by rw [hc1]; group
    have hzQ1 : QM.z = 1 := by
      rw [← MulEquiv.apply_symm_apply χ QM.z, ← hzQ, hz1, map_one]
    exact (QM.z_ne_one hzQ1).elim
  · have hc_eq : c = (zQ : G) := by
      have h2 : χ ⟨c, hcQ⟩ = χ zQ := by
        rw [h1, hzQ, MulEquiv.apply_symm_apply]
      exact congrArg Subtype.val (χ.injective h2)
    calc (g : G) * (zQ : G) = c * (g : G) := by
          simp only [c]
          group
      _ = (zQ : G) * (g : G) := by rw [hc_eq]

theorem eq_one_or_eq_of_mem_center_of_mulEquiv {P : Subgroup G}
    (χ : ↥(pCoreOf 2 P) ≃* QM) {y : G} (hy : y ∈ pCoreOf 2 P)
    (hc : ∀ q ∈ pCoreOf 2 P, y * q = q * y) :
    y = 1 ∨ y = (symmZ χ : G) := by
  have hcommQM : ∀ m : QM, χ ⟨y, hy⟩ * m = m * χ ⟨y, hy⟩ := by
    intro m
    let q : ↥(pCoreOf 2 P) := χ.symm m
    have h := hc (q : G) q.2
    have h' : χ ⟨y, hy⟩ * χ q = χ q * χ ⟨y, hy⟩ := by
      have hq_eq : (⟨y, hy⟩ : ↥(pCoreOf 2 P)) * q = q * ⟨y, hy⟩ := by
        apply Subtype.ext
        exact h
      rw [← map_mul, ← map_mul, hq_eq]
    simpa [q] using h'
  rcases QM.eq_of_comm_x (χ ⟨y, hy⟩) (fun j => hcommQM (QM.x j)) with h1 | h1
  · left
    have h2 : χ ⟨y, hy⟩ = χ (1 : ↥(pCoreOf 2 P)) := by rw [h1, map_one]
    exact congrArg Subtype.val (χ.injective h2)
  · right
    have h2 : χ ⟨y, hy⟩ = χ (χ.symm QM.z) := by
      rw [h1, MulEquiv.apply_symm_apply]
    have h3 : (⟨y, hy⟩ : ↥(pCoreOf 2 P)) = χ.symm QM.z := χ.injective h2
    exact congrArg Subtype.val h3

theorem eq_one_or_eq_of_czAct_eq_one_of_charTwo {P : Subgroup G} (hchar : CharTwo P)
    (χ : ↥(pCoreOf 2 P) ≃* QM) {g : ↥P} (hg : czActOf χ g = 1) :
    (g : G) = 1 ∨ (g : G) = (symmZ χ : G) := by
  have hC : (g : G) ∈ Subgroup.centralizer (pCoreOf 2 P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 := czActOf_apply χ g (χ ⟨q, hq⟩)
    rw [hg, MulAut.one_apply, MulEquiv.symm_apply_apply] at h1
    calc q * g = ((g : G) * q * (g : G)⁻¹) * g := by rw [← h1]
      _ = g * q := by group
  have hQ : (g : G) ∈ pCoreOf 2 P := hchar ⟨g.2, hC⟩
  exact eq_one_or_eq_of_mem_center_of_mulEquiv χ hQ fun q hq =>
    ((Subgroup.mem_centralizer_iff.mp hC) q hq).symm

theorem mem_pCoreOf_of_linePerm_eq_one_of_charTwo {P : Subgroup G} (hchar : CharTwo P)
    (χ : ↥(pCoreOf 2 P) ≃* QM) {g : ↥P} (hg : linePerm (czActOf χ g) = 1) :
    (g : G) ∈ pCoreOf 2 P := by
  obtain ⟨p, hp⟩ := eq_conj_of_linePerm_eq_one hg
  set q := χ.symm p with hq
  have hqP : (q : G) ∈ P := pCoreOf_le 2 P q.2
  have hχq : χ ⟨(q : G), q.2⟩ = p := by
    rw [Subtype.coe_eta, hq, MulEquiv.apply_symm_apply]
  have h1 : czActOf χ (⟨q, hqP⟩⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hp, czActOf_of_mem χ q.2, hχq, inv_mul_cancel]
  have h3 : ((⟨(q : G), hqP⟩⁻¹ * g : ↥P) : G) ∈ pCoreOf 2 P := by
    rcases eq_one_or_eq_of_czAct_eq_one_of_charTwo hchar χ h1 with h2 | h2
    · rw [h2]
      exact one_mem _
    · rw [h2]
      exact (χ.symm QM.z).2
  have h4 : (g : G) = (q : G) * ((⟨(q : G), hqP⟩⁻¹ * g : ↥P) : G) := by
    simp
  rw [h4]
  exact Subgroup.mul_mem _ q.2 h3

theorem range_linePerm_czAct_of_card {P : Subgroup G} (hchar : CharTwo P)
    (hP : Nat.card P = 1920) (χ : ↥(pCoreOf 2 P) ≃* QM) :
    (linePermHom.comp (czActOf χ)).range = alternatingGroup (Fin 5) := by
  set f := linePermHom.comp (czActOf χ) with hf
  have hker : f.ker = (pCoreOf 2 P).subgroupOf P := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · exact mem_pCoreOf_of_linePerm_eq_one_of_charTwo hchar χ
    · intro hg
      show linePerm (czActOf χ ⟨(g : G), pCoreOf_le 2 P hg⟩) = 1
      rw [czActOf_of_mem χ hg, linePerm_conj]
  have hcard : Nat.card f.range = 60 := by
    have h1 := Subgroup.card_ker_mul_card_range f
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 P)).toEquiv,
      Nat.card_congr χ.toEquiv, card_QM, hP] at h1
    omega
  apply Perm.eq_alternatingGroup_of_index_eq_two
  have h1 := f.range.card_mul_index
  rw [Nat.card_perm, Nat.card_fin, hcard, show Nat.factorial 5 = 120 from rfl] at h1
  omega

theorem exists_linePerm_eq_of_card {P : Subgroup G} (hchar : CharTwo P)
    (hP : Nat.card P = 1920) (χ : ↥(pCoreOf 2 P) ≃* QM) {σ : Perm (Fin 5)}
    (hσ : σ ∈ alternatingGroup (Fin 5)) :
    ∃ g : ↥P, linePerm (czActOf χ g) = σ := by
  rw [← range_linePerm_czAct_of_card hchar hP χ] at hσ
  obtain ⟨g, hg⟩ := hσ
  exact ⟨g, hg⟩

theorem linePerm_czAct_mem_of_card {P : Subgroup G} (hchar : CharTwo P)
    (hP : Nat.card P = 1920) (χ : ↥(pCoreOf 2 P) ≃* QM) (g : ↥P) :
    linePerm (czActOf χ g) ∈ alternatingGroup (Fin 5) := by
  rw [← range_linePerm_czAct_of_card hchar hP χ]
  exact ⟨g, rfl⟩

theorem exists_czAct_eq_of_card {P : Subgroup G} (hchar : CharTwo P)
    (hP : Nat.card P = 1920) (χ : ↥(pCoreOf 2 P) ≃* QM)
    {α : MulAut QM} (hα : α ∈ L0) :
    ∃ g : ↥P, czActOf χ g = α := by
  obtain ⟨g₀, hg₀⟩ := exists_linePerm_eq_of_card hchar hP χ (linePerm_mem_alternatingGroup hα)
  have h1 : linePerm (α⁻¹ * czActOf χ g₀) = 1 := by
    show linePermHom (α⁻¹ * czActOf χ g₀) = 1
    rw [map_mul, map_inv]
    show (linePerm α)⁻¹ * linePerm (czActOf χ g₀) = 1
    rw [hg₀, inv_mul_cancel]
  obtain ⟨p, hp⟩ := eq_conj_of_linePerm_eq_one h1
  set q := χ.symm p with hq
  have hqP : (q : G) ∈ P := pCoreOf_le 2 P q.2
  have hχq : χ ⟨(q : G), q.2⟩ = p := by rw [Subtype.coe_eta, hq, MulEquiv.apply_symm_apply]
  refine ⟨g₀ * ⟨q, hqP⟩⁻¹, ?_⟩
  rw [map_mul, map_inv, czActOf_of_mem χ q.2, hχq, ← hp]
  group

end General

namespace IsTypeH2

variable {G : Type} [Group G] {z : G}

@[expose]
noncomputable def czAct (χ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ≃* QM) :
    ↥(Subgroup.centralizer ({z} : Set G)) →* MulAut QM :=
  czActOf χ

variable (χ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ≃* QM)

theorem czAct_apply (h : ↥(Subgroup.centralizer ({z} : Set G))) (p : QM) :
    ((χ.symm (czAct χ h p) : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) : G) =
      (h : G) * χ.symm p * (h : G)⁻¹ := by
  exact czActOf_apply χ h p

theorem symmZ_eq_z (h : IsTypeH2 G z) : (symmZ χ : G) = z := by
  have hzQ : z ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := h.z_mem_pCoreOf
  have hc : ∀ q ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)), z * q = q * z := by
    intro q hq
    exact (Subgroup.mem_centralizer_singleton_iff.mp (pCoreOf_le 2 _ hq)).symm
  rcases eq_one_or_eq_of_mem_center_of_mulEquiv χ hzQ hc with h1 | h1
  · exact absurd h1 h.ne_one
  · exact h1.symm

theorem eq_one_or_eq_of_czAct_eq_one (h : IsTypeH2 G z)
    {g : ↥(Subgroup.centralizer ({z} : Set G))} (hg : czAct χ g = 1) :
    (g : G) = 1 ∨ (g : G) = z := by
  rcases eq_one_or_eq_of_czAct_eq_one_of_charTwo h.charTwo χ hg with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (h1.trans (symmZ_eq_z χ h))

theorem mem_pCoreOf_of_linePerm_eq_one (h : IsTypeH2 G z)
    {g : ↥(Subgroup.centralizer ({z} : Set G))} (hg : linePerm (czAct χ g) = 1) :
    (g : G) ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  exact mem_pCoreOf_of_linePerm_eq_one_of_charTwo h.charTwo χ hg

theorem exists_linePerm_eq (h : IsTypeH2 G z) {σ : Perm (Fin 5)}
    (hσ : σ ∈ alternatingGroup (Fin 5)) :
    ∃ g : ↥(Subgroup.centralizer ({z} : Set G)), linePerm (czAct χ g) = σ := by
  exact exists_linePerm_eq_of_card h.charTwo h.card_centralizer χ hσ

theorem linePerm_czAct_mem (h : IsTypeH2 G z) (g : ↥(Subgroup.centralizer ({z} : Set G))) :
    linePerm (czAct χ g) ∈ alternatingGroup (Fin 5) := by
  exact linePerm_czAct_mem_of_card h.charTwo h.card_centralizer χ g

end IsTypeH2

end CFSG.Quasithin
