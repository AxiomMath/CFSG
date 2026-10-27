module

public import CFSG.Quasithin.H13.L32NSet14Act
public import CFSG.Quasithin.Background.F8G2
public import CFSG.Quasithin.H13.L32NLem14332c
public import CFSG.Quasithin.H13.L32NLem14332f

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace L14332

section Norm

variable {G : Type*} [Group G]

theorem mem_of_norm {U V₁ H V₂ : Subgroup G} {x w : G} (hUH : U ≤ H)
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) (hcen : ∀ h ∈ H, ∀ c ∈ V₁, h * c * h⁻¹ = c)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ V₁) (hU : conjClosure V₂ H = U)
    (hxH : x ∈ H) (hx3 : x ^ 3 = 1)
    (hx : ∀ h ∈ H, ∃ k ∈ H, (∀ u ∈ U, k * u * k⁻¹ * u⁻¹ ∈ V₁) ∧
      (h⁻¹ * x * h = k * x ∨ h⁻¹ * x * h = k * x⁻¹))
    (hV : ∀ v ∈ V₂, v * (x * v * x⁻¹) * (x * x * v * (x * x)⁻¹) ∈ V₁)
    (hw : w ∈ U) (hwx : x * w * x⁻¹ * w⁻¹ ∈ V₁) (hww : w * w ∈ V₁) : w ∈ V₁ := by
  classical
  have hcU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U := fun h hh u hu =>
    (Subgroup.mem_normalizer_iff.mp (hHU hh) u).mp hu
  have hV₂U : V₂ ≤ U := hU ▸ le_conjClosure V₂ H
  have hxxH : x * x ∈ H := H.mul_mem hxH hxH
  set N : Subgroup ↥U := V₁.subgroupOf U with hNdef
  have hNn : N.Normal := ⟨fun n hn u => by
    have hn' : (n : G) ∈ V₁ := Subgroup.mem_subgroupOf.mp hn
    refine Subgroup.mem_subgroupOf.mpr ?_
    show (u : G) * n * (u : G)⁻¹ ∈ V₁
    rw [hcen u (hUH u.2) n hn']
    exact hn'⟩
  let m : G → ↥U ⧸ N := fun g => if hg : g ∈ U then ((⟨g, hg⟩ : ↥U) : ↥U ⧸ N) else 1
  have hm : ∀ {g : G} (hg : g ∈ U), m g = ((⟨g, hg⟩ : ↥U) : ↥U ⧸ N) := fun hg => dite_eq_left hg
  have hm_mul : ∀ {g g' : G}, g ∈ U → g' ∈ U → m (g * g') = m g * m g' := by
    intro g g' hg hg'
    rw [hm hg, hm hg', hm (U.mul_mem hg hg'), ← QuotientGroup.mk_mul]
    rfl
  have hm_eq : ∀ {g g' : G}, g ∈ U → g' ∈ U → (m g = m g' ↔ g⁻¹ * g' ∈ V₁) := by
    intro g g' hg hg'
    rw [hm hg, hm hg', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have hm_one : ∀ {g : G}, g ∈ U → (m g = 1 ↔ g ∈ V₁) := by
    intro g hg
    rw [hm hg, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hm1 : m 1 = 1 := (hm_one U.one_mem).mpr V₁.one_mem
  have hQc : ∀ q r : ↥U ⧸ N, q * r = r * q := by
    intro q r
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective r
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    show ((u : G) * u')⁻¹ * ((u' : G) * u) ∈ V₁
    have e : ((u : G) * u')⁻¹ * ((u' : G) * u) =
        (u' : G)⁻¹ * (u : G)⁻¹ * (u' : G)⁻¹⁻¹ * (u : G)⁻¹⁻¹ := by group
    rw [e]
    exact hcomm _ (U.inv_mem u'.2) _ (U.inv_mem u.2)
  have hgm : ∀ g ∈ H, ∀ p ∈ U, ∀ p' ∈ U, m p = m p' →
      m (g * p * g⁻¹) = m (g * p' * g⁻¹) := by
    intro g hg p hp p' hp' hpp
    rw [hm_eq hp hp'] at hpp
    rw [hm_eq (hcU g hg p hp) (hcU g hg p' hp')]
    have e : (g * p * g⁻¹)⁻¹ * (g * p' * g⁻¹) = g * (p⁻¹ * p') * g⁻¹ := by group
    rw [e, hcen g hg _ hpp]
    exact hpp
  have hrearr : ∀ p p' q q' r r' : ↥U ⧸ N,
      p * p' * (q * q') * (r * r') = p * q * r * (p' * q' * r') := by
    intro p p' q q' r r'
    calc p * p' * (q * q') * (r * r') = p * (p' * q) * q' * (r * r') := by
          simp only [mul_assoc]
      _ = p * (q * p') * q' * (r * r') := by rw [hQc p' q]
      _ = p * q * (p' * q' * r) * r' := by simp only [mul_assoc]
      _ = p * q * (r * (p' * q')) * r' := by rw [hQc (p' * q') r]
      _ = p * q * r * (p' * q' * r') := by simp only [mul_assoc]
  let f : ↥U →* ↥U ⧸ N :=
    { toFun := fun u => m u * m (x * u * x⁻¹) * m (x * x * u * (x * x)⁻¹)
      map_one' := by
        simp only [OneMemClass.coe_one, mul_one, mul_inv_cancel, hm1]
      map_mul' := fun u u' => by
        simp only [Subgroup.coe_mul]
        rw [show x * (u * u') * x⁻¹ = (x * u * x⁻¹) * (x * u' * x⁻¹) by group,
          show x * x * (u * u') * (x * x)⁻¹ =
            (x * x * u * (x * x)⁻¹) * (x * x * u' * (x * x)⁻¹) by group,
          hm_mul u.2 u'.2, hm_mul (hcU x hxH u u.2) (hcU x hxH u' u'.2),
          hm_mul (hcU _ hxxH u u.2) (hcU _ hxxH u' u'.2)]
        exact hrearr _ _ _ _ _ _ }
  have hf : ∀ u : ↥U,
      f u = 1 ↔ (u : G) * (x * u * x⁻¹) * (x * x * u * (x * x)⁻¹) ∈ V₁ := by
    intro u
    show m u * m (x * u * x⁻¹) * m (x * x * u * (x * x)⁻¹) = 1 ↔ _
    have h1 := hcU x hxH u u.2
    have h2 := hcU _ hxxH u u.2
    rw [← hm_mul u.2 h1, ← hm_mul (U.mul_mem u.2 h1) h2,
      hm_one (U.mul_mem (U.mul_mem u.2 h1) h2)]
  have hxx : x * x = x⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact hx3)
  have hgen : ∀ h ∈ H, ∀ v ∈ V₂, (h * v * h⁻¹) * (x * (h * v * h⁻¹) * x⁻¹) *
      (x * x * (h * v * h⁻¹) * (x * x)⁻¹) ∈ V₁ := by
    intro h hh v hv
    obtain ⟨k, hkH, hk, hy⟩ := hx h hh
    have hvU := hV₂U hv
    set y := h⁻¹ * x * h with hydef
    have hyH : y ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hh) hxH) hh
    have e : (h * v * h⁻¹) * (x * (h * v * h⁻¹) * x⁻¹) * (x * x * (h * v * h⁻¹) * (x * x)⁻¹) =
        h * (v * (y * v * y⁻¹) * (y * y * v * (y * y)⁻¹)) * h⁻¹ := by
      rw [hydef]
      group
    rw [e]
    suffices hs : v * (y * v * y⁻¹) * (y * y * v * (y * y)⁻¹) ∈ V₁ by
      rw [hcen h hh _ hs]
      exact hs
    have hkm : ∀ p ∈ U, m (k * p * k⁻¹) = m p := by
      intro p hp
      rw [hm_eq (hcU k hkH p hp) hp]
      have h1 := hk p⁻¹ (U.inv_mem hp)
      rw [inv_inv] at h1
      have e1 : (k * p * k⁻¹)⁻¹ * p = k * p⁻¹ * k⁻¹ * p := by group
      rw [e1]
      exact h1
    have hy1 := hcU y hyH v hvU
    have hy2 := hcU (y * y) (H.mul_mem hyH hyH) v hvU
    have hxv := hcU x hxH v hvU
    have hxxv := hcU _ hxxH v hvU
    have hNx := hV v hv
    rw [← hm_one (U.mul_mem (U.mul_mem hvU hxv) hxxv), hm_mul (U.mul_mem hvU hxv) hxxv,
      hm_mul hvU hxv] at hNx
    rw [← hm_one (U.mul_mem (U.mul_mem hvU hy1) hy2), hm_mul (U.mul_mem hvU hy1) hy2,
      hm_mul hvU hy1]
    rcases hy with hy | hy
    ·
      have h1 : m (y * v * y⁻¹) = m (x * v * x⁻¹) := by
        rw [show y * v * y⁻¹ = k * (x * v * x⁻¹) * k⁻¹ by rw [hy]; group]
        exact hkm _ hxv
      have h2 : m (y * y * v * (y * y)⁻¹) = m (x * x * v * (x * x)⁻¹) := by
        have hkxv := hcU k hkH _ hxv
        rw [show y * y * v * (y * y)⁻¹ = k * (x * (k * (x * v * x⁻¹) * k⁻¹) * x⁻¹) * k⁻¹ by
          rw [hy]; group, hkm _ (hcU x hxH _ hkxv), hgm x hxH _ hkxv _ hxv (hkm _ hxv)]
        congr 1
        group
      rw [h1, h2]
      exact hNx
    ·
      have hxiH : x⁻¹ ∈ H := H.inv_mem hxH
      have hxiv := hcU x⁻¹ hxiH v hvU
      have h1 : m (y * v * y⁻¹) = m (x * x * v * (x * x)⁻¹) := by
        rw [show y * v * y⁻¹ = k * (x⁻¹ * v * x⁻¹⁻¹) * k⁻¹ by rw [hy]; group, hkm _ hxiv, hxx]
      have h2 : m (y * y * v * (y * y)⁻¹) = m (x * v * x⁻¹) := by
        have hkxv := hcU k hkH _ hxiv
        rw [show y * y * v * (y * y)⁻¹ =
            k * (x⁻¹ * (k * (x⁻¹ * v * x⁻¹⁻¹) * k⁻¹) * x⁻¹⁻¹) * k⁻¹ by rw [hy]; group,
          hkm _ (hcU x⁻¹ hxiH _ hkxv), hgm x⁻¹ hxiH _ hkxv _ hxiv (hkm _ hxiv)]
        congr 1
        calc x⁻¹ * (x⁻¹ * v * x⁻¹⁻¹) * x⁻¹⁻¹ = (x * x * x)⁻¹ * x * v * x⁻¹ * (x * x * x) := by
              group
          _ = x * v * x⁻¹ := by rw [← pow_three', hx3]; group
      rw [h1, h2, mul_assoc, hQc (m (x * x * v * (x * x)⁻¹)) (m (x * v * x⁻¹)), ← mul_assoc]
      exact hNx
  have hker : conjClosure V₂ H ≤ f.ker.map U.subtype :=
    conjClosure_le fun h hh v hv =>
      ⟨⟨_, hcU h hh v (hV₂U hv)⟩, (hf _).mpr (hgen h hh v hv), rfl⟩
  obtain ⟨w', hw', hw'w⟩ := hker (by rw [hU]; exact hw)
  have hfw : f ⟨w, hw⟩ = 1 := by
    have : w' = ⟨w, hw⟩ := Subtype.ext hw'w
    rw [← this]
    exact hw'
  have hxw := hcU x hxH w hw
  have h1 : m (x * w * x⁻¹) = m w := by
    rw [hm_eq hxw hw]
    have e : (x * w * x⁻¹)⁻¹ * w = w⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ * w⁻¹⁻¹ := by group
    rw [e, hcen w⁻¹ (H.inv_mem (hUH hw)) _ (V₁.inv_mem hwx)]
    exact V₁.inv_mem hwx
  have h2 : m (x * x * w * (x * x)⁻¹) = m w := by
    rw [show x * x * w * (x * x)⁻¹ = x * (x * w * x⁻¹) * x⁻¹ by group,
      hgm x hxH _ hxw _ hw h1, h1]
  have hw1 : m (w * w) = 1 := (hm_one (U.mul_mem hw hw)).mpr hww
  have hfw' : m w * m (x * w * x⁻¹) * m (x * x * w * (x * x)⁻¹) = 1 := hfw
  rw [h1, h2, ← hm_mul hw hw, hw1, one_mul] at hfw'
  exact (hm_one hw).mp hfw'

end Norm

theorem perm3_pow_six : ∀ s : Equiv.Perm (Fin 3), s ^ 6 = 1 := by decide

theorem perm3_cube_mul : ∀ s t : Equiv.Perm (Fin 3), s ^ 3 = 1 → t ^ 3 = 1 → (s * t) ^ 3 = 1 := by
  decide

theorem perm3sq_cube_mul {s t : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)} (hs : s ^ 3 = 1)
    (ht : t ^ 3 = 1) : (s * t) ^ 3 = 1 := by
  have h1 : s.1 ^ 3 = 1 := by rw [← Prod.pow_fst, hs, Prod.fst_one]
  have h2 : s.2 ^ 3 = 1 := by rw [← Prod.pow_snd, hs, Prod.snd_one]
  have h3 : t.1 ^ 3 = 1 := by rw [← Prod.pow_fst, ht, Prod.fst_one]
  have h4 : t.2 ^ 3 = 1 := by rw [← Prod.pow_snd, ht, Prod.snd_one]
  refine Prod.ext ?_ ?_
  · rw [Prod.pow_fst, Prod.fst_mul, Prod.fst_one]
    exact perm3_cube_mul _ _ h1 h3
  · rw [Prod.pow_snd, Prod.snd_mul, Prod.snd_one]
    exact perm3_cube_mul _ _ h2 h4

theorem perm3sq_cube_of_odd {s : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)} {m : ℕ} (hm : Odd m)
    (h : s ^ m = 1) : s ^ 3 = 1 := by
  have h6 : s ^ 6 = 1 := Prod.ext (by rw [Prod.pow_fst, perm3_pow_six, Prod.fst_one])
    (by rw [Prod.pow_snd, perm3_pow_six, Prod.snd_one])
  have hodd : Odd (orderOf s) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h)
  have key : ∀ n : ℕ, n ∣ 6 → Odd n → n ∣ 3 := by
    intro n hn hn'
    have h1 : n ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨hn, by norm_num⟩
    rw [show Nat.divisors 6 = {1, 2, 3, 6} by decide] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with rfl | rfl | rfl | rfl
    · exact one_dvd _
    · exact absurd hn' (by decide)
    · exact dvd_refl _
    · exact absurd hn' (by decide)
  exact orderOf_dvd_iff_pow_eq_one.mp (key _ (orderOf_dvd_of_pow_eq_one h6) hodd)

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g a : G}
  {D : HatModelU (fsuU T V)}

theorem exists_setting (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h : Hyp14310One G T L V) (hV₂ : IsL32NPlane T V V₂) :
    ∃ _ : IsMulCommutative ↥V, L32NSet14.Setting G T L V V₂ := by
  have hL := h1332 G T L h.hyp.h13 L h.hyp.h13.faithful
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hL.2.1.1
  have hcc : conjClosure L T = L :=
    le_antisymm
      (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.1 (hTL ht) l).1 hl)
      (le_conjClosure L T)
  have hIrr : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V := by
    have := h.fsu.irrPlus
    rwa [hcc] at this
  obtain ⟨-, -, -, hc, hmod⟩ := hL.2.2.1.2 V hIrr
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hIrr.2.2.1
  have hne : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    have h1 : ⁅V, L⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle)
    exact hIrr.2.1 (hIrr.2.2.2.1.symm.trans h1)
  obtain ⟨hnat, hCV⟩ := modules13_3_2_of_L32 h.hyp.linear hLV hne hmod
  exact ⟨hc, ⟨h1222, h1332, h1334, h.hyp.h13, hIrr, hCV,
    ⟨hV₂.2, hV₂.1.1, hV₂.1.2.2, hV₂.1.2.1⟩, h.hyp.linear, hnat⟩⟩

theorem card_zU_eq_four_of_case_i (h14323 : Lemma14323Rest) (C : Ctx14332 G T L V V₂ g a D)
    (hd : Module.finrank (ZMod 2) D.V = 4) (hi : Case14323i T L V g D) :
    Nat.card ↥(centerOf (fsuU T V)) = 4 := by
  have := finite_linearEquiv D
  obtain ⟨-, -, ⟨hrel, -⟩, -⟩ := h14323 G T L V C.hyp V₂ g C.plane C.gP C.gN D hd
  obtain ⟨e⟩ := hi.iso
  have h36 : Nat.card ↥(D.img (l32nH T V)) = 36 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin]
    rfl
  have hXH : D.img (CFSG.conjugate (l32nW T V V₂) g) ≤ D.img (l32nH T V) := by
    intro γ hγ
    obtain ⟨y, hy, hyN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact L128A.HatU.rho_mem_img D (C.Wg_le hy) hyN
  have hW2 : IsPGroup 2 ↥(CFSG.conjugate (l32nW T V V₂) g) :=
    (C.U2.to_le inf_le_left).map (MulAut.conj g⁻¹).toMonoidHom
  have hX2 : IsPGroup 2 ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) := by
    have hW2' : IsPGroup 2
        ↥((CFSG.conjugate (l32nW T V V₂) g).subgroupOf (Subgroup.normalizer (fsuU T V : Set G))) :=
      hW2.of_equiv (Subgroup.subgroupOfEquivOfLe
        (C.Wg_le.trans (l32nH_le_normalizer_fsuU T V))).symm
    exact hW2'.map D.ρ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hX2.exists_card_eq
  have hdvd := Subgroup.card_dvd_of_le hXH
  rw [hm, h36] at hdvd
  have hm2 : m ≤ 2 := by
    by_contra hm3
    push Not at hm3
    have h8 : 2 ^ 3 ∣ 36 := (Nat.pow_dvd_pow 2 hm3).trans hdvd
    norm_num at h8
  have hX4 : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) ≤ 4 := by
    rw [hm]
    calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
      _ = 4 := by norm_num
  have hmul := Subgroup.relIndex_mul_card (H := D.img (CFSG.conjugate (centerOf (fsuU T V)) g))
    (K := D.img (CFSG.conjugate (l32nW T V V₂) g))
  rw [inf_eq_left.mpr (img_zU_le C), hrel] at hmul
  have hZ := C.card_zU
  have h4 := four_le_card_zU C
  omega

omit [Finite G] in
theorem lOne_le_l32nH : lOne L (fsuV1 T V) ≤ l32nH T V :=
  (oTwoUpper_le _).trans inf_le_right

theorem card_img_lOne_dvd_three [IsMulCommutative ↥V] (S : L32NSet14.Setting G T L V V₂)
    (hi : Case14323i T L V g D) : Nat.card ↥(D.img (lOne L (fsuV1 T V))) ∣ 3 := by
  have := finite_linearEquiv D
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hi.iso
  have hL₁H : lOne L (fsuV1 T V) ≤ l32nH T V := lOne_le_l32nH
  set F : ↥(lOne L (fsuV1 T V)) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
    (e : ↥(D.img (l32nH T V)) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)).comp
      ((imgHom D).comp (Subgroup.inclusion hL₁H)) with hF
  have hF3 : ∀ l : ↥(lOne L (fsuV1 T V)), F l ^ 3 = 1 := by
    rintro ⟨l, hl⟩
    refine Subgroup.closure_induction
      (k := {y | y ∈ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) ∧ Odd (orderOf y)})
      (p := fun l hl => F ⟨l, hl⟩ ^ 3 = 1) ?_ ?_ ?_ ?_ hl
    · intro y hy
      have hy1 : (⟨y, Subgroup.subset_closure hy⟩ : ↥(lOne L (fsuV1 T V))) ^ orderOf y = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_orderOf_eq_one y)
      refine perm3sq_cube_of_odd hy.2 ?_
      rw [← map_pow, hy1, map_one]
    · show F 1 ^ 3 = 1
      rw [map_one, one_pow]
    · intro y y' hy hy' ih ih'
      show F (⟨y, hy⟩ * ⟨y', hy'⟩) ^ 3 = 1
      rw [map_mul]
      exact perm3sq_cube_mul ih ih'
    · intro y hy ih
      show F (⟨y, hy⟩ : ↥(lOne L (fsuV1 T V)))⁻¹ ^ 3 = 1
      rw [map_inv, inv_pow, ih, inv_one]
  have hO : pCoreOf 2 (lOne L (fsuV1 T V)) ≤ l32nCHat T V := by
    intro q hq
    have hqL : q ∈ lOne L (fsuV1 T V) := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (lOne L (fsuV1 T V))) ⟨q, hq⟩
    have hk' : (⟨q, hqL⟩ : ↥(lOne L (fsuV1 T V))) ^ 2 ^ k = 1 := Subtype.ext (by
      have := congrArg Subtype.val hk
      simpa using this)
    have h2 : F ⟨q, hqL⟩ ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
    have ho : orderOf (F ⟨q, hqL⟩) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
        (orderOf_dvd_of_pow_eq_one (hF3 _)) (orderOf_dvd_of_pow_eq_one h2)
    have hF1 : F ⟨q, hqL⟩ = 1 := orderOf_eq_one_iff.mp ho
    have h1 : imgHom D ⟨q, hL₁H hqL⟩ = 1 := e.map_eq_one_iff.mp hF1
    have h1' := congrArg Subtype.val h1
    rw [imgHom_apply] at h1'
    exact (rho_eq_one_iff_mem (hL₁H hqL) _).mp h1'
  have hcard : Nat.card ↥(D.img (lOne L (fsuV1 T V))) =
      (l32nCHat T V).relIndex (lOne L (fsuV1 T V)) := by
    refine L128A.HatU.card_img_eq_relIndex D (hL₁H.trans (l32nH_le_normalizer_fsuU T V))
      fun y hy => ?_
    constructor
    · rintro ⟨hyN, h1⟩
      exact (rho_eq_one_iff_mem (hL₁H hy) hyN).mp h1
    · intro hyC
      exact ⟨l32nH_le_normalizer_fsuU T V (hL₁H hy), (rho_eq_one_iff_mem (hL₁H hy) _).mpr hyC⟩
  rw [hcard]
  have h3 : (pCoreOf 2 (lOne L (fsuV1 T V))).relIndex (lOne L (fsuV1 T V)) = 3 := by
    rw [lOne_eq_L₁Of]
    exact S.Lp3
  rw [← h3]
  exact Subgroup.relIndex_dvd_of_le_left _ hO

theorem not_case_i (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h14323 : Lemma14323Rest) (C : Ctx14332 G T L V V₂ g a D)
    (hd : Module.finrank (ZMod 2) D.V = 4) (hi : Case14323i T L V g D) : False := by
  have := finite_linearEquiv D
  obtain ⟨_, S⟩ := exists_setting h1332 h1334 h1222 C.hyp C.plane
  have h4 := card_zU_eq_four_of_case_i h14323 C hd hi
  have hCQ : l32nCHat T V = centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) := by
    rw [C.q_tilde, C.q_eq h4]
  have hk : ∀ k ∈ l32nH T V, ∀ hkN : k ∈ Subgroup.normalizer (fsuU T V : Set G),
      D.ρ ⟨k, hkN⟩ = 1 → ∀ u ∈ fsuU T V, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V := by
    intro k hkH hkN h1
    have hkC : k ∈ centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) := by
      rw [← hCQ]
      exact (rho_eq_one_iff_mem hkH hkN).mp h1
    obtain ⟨-, -, hkc⟩ := hkC
    exact hkc
  obtain ⟨z, -, b, hz, hz1, -, -, hbV, hbV₂⟩ := S.exists_basis
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hzV₂ : z ∈ V₂ := C.plane.2 hz
  have haV : a ∈ V := C.plane.1.1 C.aV₂
  obtain ⟨x, hxL, hx3, hxz, hxa, hxb⟩ := S.exists_rot hzV haV hbV
    (fun h => C.a1 (h ▸ one_mem _)) (fun h => hbV₂ (h ▸ one_mem _))
    (fun h => C.a1 (h ▸ hz)) (fun h => hbV₂ (h ▸ hzV₂)) (fun h => hbV₂ (h ▸ C.aV₂))
    (fun h => hbV₂ (h ▸ mul_mem hzV₂ C.aV₂))
  have hxH : x ∈ l32nH T V := S.mem_g1 hz hz1 hxz
  have hxL₁ : x ∈ lOne L (fsuV1 T V) := by
    rw [lOne_eq_L₁Of]
    exact Subgroup.subset_closure ⟨⟨hxL, hxH⟩, 3, by decide, hx3⟩
  have hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G) := l32nH_le_normalizer_fsuU T V hxH
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = D.ρ ⟨x, hxN⟩ := ⟨_, rfl⟩
  have hγ1 : γ ≠ 1 := by
    intro h1
    have hba := hk x hxH hxN (hγ ▸ h1) a C.aU
    rw [hxa] at hba
    apply hbV₂
    have : b * a⁻¹ * a ∈ V₂ := V₂.mul_mem (C.plane.2 hba) C.aV₂
    rwa [inv_mul_cancel_right] at this
  have hγ3 : γ ^ 3 = 1 := by
    rw [hγ, ← map_pow]
    have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hx3)
    rw [this, map_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf γ = 3 := orderOf_eq_prime hγ3 hγ1
  have hγL : γ ∈ D.img (lOne L (fsuV1 T V)) := hγ ▸ L128A.HatU.rho_mem_img D hxL₁ hxN
  have hL₁ : D.img (lOne L (fsuV1 T V)) = Subgroup.zpowers γ := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hγL) ?_).symm
    rw [Nat.card_zpowers, hord]
    exact Nat.le_of_dvd (by norm_num) (card_img_lOne_dvd_three S hi)
  have hxdich : ∀ h ∈ l32nH T V, ∃ k ∈ l32nH T V,
      (∀ u ∈ fsuU T V, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V) ∧
      (h⁻¹ * x * h = k * x ∨ h⁻¹ * x * h = k * x⁻¹) := by
    intro h hh
    have hhN := l32nH_le_normalizer_fsuU T V hh
    have hyH : h⁻¹ * x * h ∈ l32nH T V := mul_mem (mul_mem (inv_mem hh) hxH) hh
    have hyN := l32nH_le_normalizer_fsuU T V hyH
    have hρy : D.ρ ⟨h⁻¹ * x * h, hyN⟩ = (D.ρ ⟨h, hhN⟩)⁻¹ * γ * (D.ρ ⟨h, hhN⟩)⁻¹⁻¹ := by
      rw [inv_inv, hγ, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hyL : D.ρ ⟨h⁻¹ * x * h, hyN⟩ ∈ Subgroup.zpowers γ := by
      rw [← hL₁, hρy]
      exact (Subgroup.mem_normalizer_iff.mp (hi.l1_normal ((D.img (l32nH T V)).inv_mem
        (L128A.HatU.rho_mem_img D hh hhN))) γ).mp hγL
    have hy1 : D.ρ ⟨h⁻¹ * x * h, hyN⟩ ≠ 1 := by
      intro h1
      rw [hρy, inv_inv] at h1
      apply hγ1
      calc γ = D.ρ ⟨h, hhN⟩ * ((D.ρ ⟨h, hhN⟩)⁻¹ * γ * D.ρ ⟨h, hhN⟩) * (D.ρ ⟨h, hhN⟩)⁻¹ := by
            group
        _ = 1 := by rw [h1]; group
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, hord, Finset.mem_image] at hyL
    obtain ⟨j, hj, hjy⟩ := hyL
    rw [Finset.mem_range] at hj
    have hk1 : h⁻¹ * x * h * x⁻¹ ∈ l32nH T V := mul_mem hyH (inv_mem hxH)
    have hk2 : h⁻¹ * x * h * x ∈ l32nH T V := mul_mem hyH hxH
    interval_cases j
    · exact absurd (hjy.symm.trans (pow_zero γ)) hy1
    · refine ⟨h⁻¹ * x * h * x⁻¹, hk1,
        hk _ hk1 (l32nH_le_normalizer_fsuU T V hk1) ?_, Or.inl (by group)⟩
      have e : (⟨h⁻¹ * x * h * x⁻¹, l32nH_le_normalizer_fsuU T V hk1⟩ :
          ↥(Subgroup.normalizer (fsuU T V : Set G))) = ⟨h⁻¹ * x * h, hyN⟩ * ⟨x, hxN⟩⁻¹ := rfl
      rw [e, map_mul, map_inv, ← hγ, ← hjy, pow_one, mul_inv_cancel]
    · refine ⟨h⁻¹ * x * h * x, hk2,
        hk _ hk2 (l32nH_le_normalizer_fsuU T V hk2) ?_, Or.inr (by group)⟩
      have e : (⟨h⁻¹ * x * h * x, l32nH_le_normalizer_fsuU T V hk2⟩ :
          ↥(Subgroup.normalizer (fsuU T V : Set G))) = ⟨h⁻¹ * x * h, hyN⟩ * ⟨x, hxN⟩ := rfl
      rw [e, map_mul, ← hγ, ← hjy, ← pow_succ]
      exact hγ3
  have hV : ∀ v ∈ V₂, v * (x * v * x⁻¹) * (x * x * v * (x * x)⁻¹) ∈ fsuV1 T V := by
    intro v hv
    rcases C.V₂_cases v hv with hv1 | ⟨c, hc, rfl⟩
    · rw [C.H_V1 x hxH v hv1, C.H_V1 (x * x) (mul_mem hxH hxH) v hv1,
        S.mul_self_V (Subgroup.mem_inf.mp hv1).1, one_mul]
      exact hv1
    · have hcV : c ∈ V := (Subgroup.mem_inf.mp hc).1
      have hxc := C.H_V1 x hxH c hc
      have e1 : x * (a * c) * x⁻¹ = b * c := by
        rw [show x * (a * c) * x⁻¹ = (x * a * x⁻¹) * (x * c * x⁻¹) by group, hxa, hxc]
      have e2 : x * x * (a * c) * (x * x)⁻¹ = a * b * c := by
        rw [show x * x * (a * c) * (x * x)⁻¹ = x * (x * (a * c) * x⁻¹) * x⁻¹ by group, e1,
          show x * (b * c) * x⁻¹ = (x * b * x⁻¹) * (x * c * x⁻¹) by group, hxb, hxc]
      have hcb : c * b = b * c := S.comm_V hcV hbV
      have e3 : a * c * (b * c) * (a * b * c) = c := by
        calc a * c * (b * c) * (a * b * c) = a * (c * b) * c * (a * b * c) := by group
          _ = a * (b * c) * c * (a * b * c) := by rw [hcb]
          _ = a * b * (c * c) * (a * b * c) := by group
          _ = a * b * (a * b) * c := by rw [S.mul_self_V hcV, mul_one]; group
          _ = c := by rw [S.mul_self_V (mul_mem haV hbV), one_mul]
      rw [e1, e2, e3]
      exact hc
  obtain ⟨w, hwZ, hwV₁⟩ := IsConcreteLE.exists_of_lt C.lt
  have hwU : w ∈ fsuU T V := (Subgroup.mem_inf.mp hwZ).1
  exact hwV₁ (mem_of_norm (V₂ := V₂) C.U_le (l32nH_le_normalizer_fsuU T V) C.H_V1
    (fun u hu v hv => by simpa [commutatorElement_def] using C.comm u hu v hv)
    (lemma12_8_8_six h1222 C.setting).symm hxH hx3 hxdich hV hwU
    (C.conj_zU_mem h4 x hxH w hwZ) (C.sq w hwU))

end L14332

end CFSG.Quasithin.H13
