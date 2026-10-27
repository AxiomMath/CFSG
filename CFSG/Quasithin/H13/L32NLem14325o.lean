module

public import CFSG.Quasithin.H13.L32NLem14325n

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.Vol2.Ch10.SecF

namespace L14325

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

section Norm

variable {G' : Type*} [Group G']

theorem mem_of_norm' {U N₀ H V₂ : Subgroup G'} {x w : G'} (hUH : U ≤ H)
    (hHU : H ≤ Subgroup.normalizer (U : Set G')) (hcen : ∀ h ∈ H, ∀ c ∈ N₀, h * c * h⁻¹ ∈ N₀)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ N₀) (hU : conjClosure V₂ H = U)
    (hxH : x ∈ H) (hx3 : x ^ 3 = 1)
    (hx : ∀ h ∈ H, ∃ k ∈ H, (∀ u ∈ U, k * u * k⁻¹ * u⁻¹ ∈ N₀) ∧
      (h⁻¹ * x * h = k * x ∨ h⁻¹ * x * h = k * x⁻¹))
    (hV : ∀ v ∈ V₂, v * (x * v * x⁻¹) * (x * x * v * (x * x)⁻¹) ∈ N₀)
    (hw : w ∈ U) (hwx : x * w * x⁻¹ * w⁻¹ ∈ N₀) (hww : w * w ∈ N₀) : w ∈ N₀ := by
  classical
  have hcU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U := fun h hh u hu =>
    (Subgroup.mem_normalizer_iff.mp (hHU hh) u).mp hu
  have hV₂U : V₂ ≤ U := hU ▸ le_conjClosure V₂ H
  have hxxH : x * x ∈ H := H.mul_mem hxH hxH
  set N : Subgroup ↥U := N₀.subgroupOf U with hNdef
  have hNn : N.Normal := ⟨fun n hn u => by
    have hn' : (n : G') ∈ N₀ := Subgroup.mem_subgroupOf.mp hn
    refine Subgroup.mem_subgroupOf.mpr ?_
    show (u : G') * n * (u : G')⁻¹ ∈ N₀
    exact hcen u (hUH u.2) n hn'⟩
  let m : G' → ↥U ⧸ N := fun g => if hg : g ∈ U then ((⟨g, hg⟩ : ↥U) : ↥U ⧸ N) else 1
  have hm : ∀ {g : G'} (hg : g ∈ U), m g = ((⟨g, hg⟩ : ↥U) : ↥U ⧸ N) := fun hg => dite_eq_left hg
  have hm_mul : ∀ {g g' : G'}, g ∈ U → g' ∈ U → m (g * g') = m g * m g' := by
    intro g g' hg hg'
    rw [hm hg, hm hg', hm (U.mul_mem hg hg'), ← QuotientGroup.mk_mul]
    rfl
  have hm_eq : ∀ {g g' : G'}, g ∈ U → g' ∈ U → (m g = m g' ↔ g⁻¹ * g' ∈ N₀) := by
    intro g g' hg hg'
    rw [hm hg, hm hg', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have hm_one : ∀ {g : G'}, g ∈ U → (m g = 1 ↔ g ∈ N₀) := by
    intro g hg
    rw [hm hg, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hm1 : m 1 = 1 := (hm_one U.one_mem).mpr N₀.one_mem
  have hQc : ∀ q r : ↥U ⧸ N, q * r = r * q := by
    intro q r
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective r
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    show ((u : G') * u')⁻¹ * ((u' : G') * u) ∈ N₀
    have e : ((u : G') * u')⁻¹ * ((u' : G') * u) =
        (u' : G')⁻¹ * (u : G')⁻¹ * (u' : G')⁻¹⁻¹ * (u : G')⁻¹⁻¹ := by group
    rw [e]
    exact hcomm _ (U.inv_mem u'.2) _ (U.inv_mem u.2)
  have hgm : ∀ g ∈ H, ∀ p ∈ U, ∀ p' ∈ U, m p = m p' →
      m (g * p * g⁻¹) = m (g * p' * g⁻¹) := by
    intro g hg p hp p' hp' hpp
    rw [hm_eq hp hp'] at hpp
    rw [hm_eq (hcU g hg p hp) (hcU g hg p' hp')]
    have e : (g * p * g⁻¹)⁻¹ * (g * p' * g⁻¹) = g * (p⁻¹ * p') * g⁻¹ := by group
    rw [e]
    exact hcen g hg _ hpp
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
      f u = 1 ↔ (u : G') * (x * u * x⁻¹) * (x * x * u * (x * x)⁻¹) ∈ N₀ := by
    intro u
    show m u * m (x * u * x⁻¹) * m (x * x * u * (x * x)⁻¹) = 1 ↔ _
    have h1 := hcU x hxH u u.2
    have h2 := hcU _ hxxH u u.2
    rw [← hm_mul u.2 h1, ← hm_mul (U.mul_mem u.2 h1) h2,
      hm_one (U.mul_mem (U.mul_mem u.2 h1) h2)]
  have hxx : x * x = x⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact hx3)
  have hgen : ∀ h ∈ H, ∀ v ∈ V₂, (h * v * h⁻¹) * (x * (h * v * h⁻¹) * x⁻¹) *
      (x * x * (h * v * h⁻¹) * (x * x)⁻¹) ∈ N₀ := by
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
    suffices hs : v * (y * v * y⁻¹) * (y * y * v * (y * y)⁻¹) ∈ N₀ by
      exact hcen h hh _ hs
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
    rw [e]
    exact hcen w⁻¹ (H.inv_mem (hUH hw)) _ (N₀.inv_mem hwx)
  have h2 : m (x * x * w * (x * x)⁻¹) = m w := by
    rw [show x * x * w * (x * x)⁻¹ = x * (x * w * x⁻¹) * x⁻¹ by group,
      hgm x hxH _ hxw _ hw h1, h1]
  have hw1 : m (w * w) = 1 := (hm_one (U.mul_mem hw hw)).mpr hww
  have hfw' : m w * m (x * w * x⁻¹) * m (x * x * w * (x * x)⁻¹) = 1 := hfw
  rw [h1, h2, ← hm_mul hw hw, hw1, one_mul] at hfw'
  exact (hm_one hw).mp hfw'


end Norm

namespace CtxI

variable (C : CtxI G T L V V₂ g D)
include C

theorem img_kI_normal {γ δ : D.V ≃ₗ[ZMod 2] D.V} (hγ : γ ∈ D.img (l32nH T V))
    (hδ : δ ∈ D.img (kI T V g)) : γ * δ * γ⁻¹ ∈ D.img (kI T V g) := by
  obtain ⟨h, hh, hhN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
  obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hδ
  have hk' : h * k * h⁻¹ ∈ kI T V g :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_kI hh) k).mp hk
  have e1 : (⟨h * k * h⁻¹, L14332.l32nH_le_normalizer_fsuU T V (C.kI_le hk')⟩ :
      ↥(Subgroup.normalizer (fsuU T V : Set G))) = ⟨h, hhN⟩ * ⟨k, hkN⟩ * (⟨h, hhN⟩)⁻¹ := rfl
  have := L128A.HatU.rho_mem_img D hk' (L14332.l32nH_le_normalizer_fsuU T V (C.kI_le hk'))
  rwa [e1, map_mul, map_mul, map_inv] at this

theorem not_lOne_le : ¬ D.img (lOne L (fsuV1 T V)) ≤ D.img (kI T V g) := by
  intro hle
  have := L14332.finite_linearEquiv D
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eH⟩ := C.hi.iso
  obtain ⟨eK⟩ := C.iso
  have h36 : Nat.card ↥(D.img (l32nH T V)) = 36 := by
    rw [Nat.card_congr eH.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin]
    rfl
  have h6 : Nat.card ↥(D.img (kI T V g)) = 6 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hTH : D.img T ≤ D.img (l32nH T V) := by
    intro γ hγ
    obtain ⟨t, ht, htN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact L128A.HatU.rho_mem_img D (C.ctx.T_le ht) htN
  have hT2 : IsPGroup 2 ↥T := C.ctx.hyp.fsu.sylow.1
  have hT2' : IsPGroup 2 ↥(T.subgroupOf (Subgroup.normalizer (fsuU T V : Set G))) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe
      (C.ctx.T_le.trans (L14332.l32nH_le_normalizer_fsuU T V))).symm
  have hX2 : IsPGroup 2 ↥(D.img T) := hT2'.map D.ρ
  obtain ⟨m, hm⟩ := hX2.exists_card_eq
  have hdvd := Subgroup.card_dvd_of_le hTH
  rw [hm, h36] at hdvd
  have hm2 : m ≤ 2 := by
    by_contra hm3
    push Not at hm3
    have h8 : 2 ^ 3 ∣ 36 := (Nat.pow_dvd_pow 2 hm3).trans hdvd
    norm_num at h8
  have hT4 : Nat.card ↥(D.img T) ≤ 4 := by
    rw [hm]
    calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
      _ = 4 := by norm_num
  have hsup : D.img (kI T V g) ⊔ D.img T = D.img (l32nH T V) := by
    rw [← C.sup, sup_eq_left.mpr hle]
  have hnorm : D.img T ≤ Subgroup.normalizer (D.img (kI T V g) : Set (D.V ≃ₗ[ZMod 2] D.V)) := by
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro δ
    refine ⟨fun hδ => C.img_kI_normal (hTH hγ) hδ, fun hδ => ?_⟩
    have := C.img_kI_normal ((D.img (l32nH T V)).inv_mem (hTH hγ)) hδ
    have e1 : γ⁻¹ * (γ * δ * γ⁻¹) * γ⁻¹⁻¹ = δ := by group
    rwa [e1] at this
  have hcard := L32NSet14.card_sup_mul_card_inf hnorm
  rw [sup_comm, hsup, h36, h6] at hcard
  have hpos : 0 < Nat.card ↥(D.img T ⊓ D.img (kI T V g)) := Nat.card_pos
  have : 36 ≤ 24 := by
    calc 36 ≤ 36 * Nat.card ↥(D.img T ⊓ D.img (kI T V g)) := Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card ↥(D.img T) * 6 := hcard
      _ ≤ 4 * 6 := Nat.mul_le_mul_right _ hT4
      _ = 24 := by norm_num
  omega

end CtxI

namespace CtxI.TransData

variable {C : CtxI G T L V V₂ g D} {x c : G} (X : TransData C x c)
include X

theorem false (h64 : G64.LemmaG64) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) : False := by
  have := L14332.finite_linearEquiv D
  obtain ⟨_, S⟩ := L14332.exists_setting h1332 h1334 h1222 C.ctx.hyp C.ctx.plane
  have hU : conjClosure V₂ (l32nH T V) = fsuU T V := (lemma12_8_8_six h1222 C.ctx.setting).symm
  have hT : QuasithinUnique.IsSylowTwoOf T (l32nH T V) :=
    C.ctx.hyp.isSylowTwoOf_l32nH (stmtL32NModule_of_inputs h1332 h1334)
  have hVZ : V ⊓ centerOf (fsuU T V) = fsuV1 T V := lemma12_8_8_three h1222 h12213 C.ctx.setting
  have hE : ∀ k ∈ l32nH T V, ∀ hkN : k ∈ Subgroup.normalizer (fsuU T V : Set G),
      D.ρ ⟨k, hkN⟩ = 1 → ∀ u ∈ fsuU T V, k * u * k⁻¹ * u⁻¹ ∈ nK T V g :=
    fun k hkH hkN h1 u hu => X.cHat_U h64 hT hU ((L14332.rho_eq_one_iff_mem hkH hkN).mp h1) hu
  obtain ⟨z, a, b, hz, hz1, haV₂, ha1, hbV, hbV₂⟩ := S.exists_basis
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hzV₂ : z ∈ V₂ := C.ctx.plane.2 hz
  have haV : a ∈ V := C.ctx.plane.1.1 haV₂
  obtain ⟨r, hrL, hr3, hrz, hra, hrb⟩ := S.exists_rot hzV haV hbV
    (fun h => ha1 (h ▸ one_mem _)) (fun h => hbV₂ (h ▸ one_mem _))
    (fun h => ha1 (h ▸ hz)) (fun h => hbV₂ (h ▸ hzV₂)) (fun h => hbV₂ (h ▸ haV₂))
    (fun h => hbV₂ (h ▸ mul_mem hzV₂ haV₂))
  have hrH : r ∈ l32nH T V := S.mem_g1 hz hz1 hrz
  have hrL₁ : r ∈ lOne L (fsuV1 T V) := by
    rw [lOne_eq_L₁Of]
    exact Subgroup.subset_closure ⟨⟨hrL, hrH⟩, 3, by decide, hr3⟩
  have hrN : r ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    L14332.l32nH_le_normalizer_fsuU T V hrH
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = D.ρ ⟨r, hrN⟩ := ⟨_, rfl⟩
  have hγ1 : γ ≠ 1 := by
    intro h1
    have hra' := hE r hrH hrN (hγ ▸ h1) a (C.ctx.V_U haV)
    rw [hra] at hra'
    have hba : b * a⁻¹ ∈ fsuV1 T V := by
      rw [← hVZ]
      exact ⟨V.mul_mem hbV (V.inv_mem haV), hra'.1⟩
    apply hbV₂
    have : b * a⁻¹ * a ∈ V₂ := V₂.mul_mem (C.ctx.plane.2 hba) haV₂
    rwa [inv_mul_cancel_right] at this
  have hγ3 : γ ^ 3 = 1 := by
    rw [hγ, ← map_pow]
    have : (⟨r, hrN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hr3)
    rw [this, map_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf γ = 3 := orderOf_eq_prime hγ3 hγ1
  have hγL : γ ∈ D.img (lOne L (fsuV1 T V)) := hγ ▸ L128A.HatU.rho_mem_img D hrL₁ hrN
  have hL₁ : D.img (lOne L (fsuV1 T V)) = Subgroup.zpowers γ := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hγL) ?_).symm
    rw [Nat.card_zpowers, hord]
    exact Nat.le_of_dvd (by norm_num) (L14332.card_img_lOne_dvd_three S C.hi)
  have hxdich : ∀ h ∈ l32nH T V, ∃ k ∈ l32nH T V,
      (∀ u ∈ fsuU T V, k * u * k⁻¹ * u⁻¹ ∈ nK T V g) ∧
      (h⁻¹ * r * h = k * r ∨ h⁻¹ * r * h = k * r⁻¹) := by
    intro h hh
    have hhN := L14332.l32nH_le_normalizer_fsuU T V hh
    have hyH : h⁻¹ * r * h ∈ l32nH T V := mul_mem (mul_mem (inv_mem hh) hrH) hh
    have hyN := L14332.l32nH_le_normalizer_fsuU T V hyH
    have hρy : D.ρ ⟨h⁻¹ * r * h, hyN⟩ = (D.ρ ⟨h, hhN⟩)⁻¹ * γ * (D.ρ ⟨h, hhN⟩)⁻¹⁻¹ := by
      rw [inv_inv, hγ, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hyL : D.ρ ⟨h⁻¹ * r * h, hyN⟩ ∈ Subgroup.zpowers γ := by
      rw [← hL₁, hρy]
      exact (Subgroup.mem_normalizer_iff.mp (C.l1_normal ((D.img (l32nH T V)).inv_mem
        (L128A.HatU.rho_mem_img D hh hhN))) γ).mp hγL
    have hy1 : D.ρ ⟨h⁻¹ * r * h, hyN⟩ ≠ 1 := by
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
    have hk1 : h⁻¹ * r * h * r⁻¹ ∈ l32nH T V := mul_mem hyH (inv_mem hrH)
    have hk2 : h⁻¹ * r * h * r ∈ l32nH T V := mul_mem hyH hrH
    interval_cases j
    · exact absurd (hjy.symm.trans (pow_zero γ)) hy1
    · refine ⟨h⁻¹ * r * h * r⁻¹, hk1,
        hE _ hk1 (L14332.l32nH_le_normalizer_fsuU T V hk1) ?_, Or.inl (by group)⟩
      have e : (⟨h⁻¹ * r * h * r⁻¹, L14332.l32nH_le_normalizer_fsuU T V hk1⟩ :
          ↥(Subgroup.normalizer (fsuU T V : Set G))) = ⟨h⁻¹ * r * h, hyN⟩ * ⟨r, hrN⟩⁻¹ := rfl
      rw [e, map_mul, map_inv, ← hγ, ← hjy, pow_one, mul_inv_cancel]
    · refine ⟨h⁻¹ * r * h * r, hk2,
        hE _ hk2 (L14332.l32nH_le_normalizer_fsuU T V hk2) ?_, Or.inr (by group)⟩
      have e : (⟨h⁻¹ * r * h * r, L14332.l32nH_le_normalizer_fsuU T V hk2⟩ :
          ↥(Subgroup.normalizer (fsuU T V : Set G))) = ⟨h⁻¹ * r * h, hyN⟩ * ⟨r, hrN⟩ := rfl
      rw [e, map_mul, ← hγ, ← hjy, ← pow_succ]
      exact hγ3
  have hidx : (fsuV1 T V).relIndex V₂ = 2 := by
    have := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := V₂)
    rw [inf_eq_left.mpr C.ctx.plane.2, C.ctx.card_V1, C.ctx.plane.1.2.1] at this
    omega
  have hV₂c : ∀ v ∈ V₂, v ∈ fsuV1 T V ∨ ∃ c' ∈ fsuV1 T V, v = a * c' := by
    intro v hv
    by_cases hv1 : v ∈ fsuV1 T V
    · exact Or.inl hv1
    right
    have hm := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a⁻¹, V₂.inv_mem haV₂⟩)
      (b := ⟨v, hv⟩)).mpr (iff_of_false (fun hm => ha1 (by
        have := (fsuV1 T V).inv_mem (Subgroup.mem_subgroupOf.mp hm)
        rwa [inv_inv] at this)) (fun hm => hv1 (Subgroup.mem_subgroupOf.mp hm)))
    exact ⟨a⁻¹ * v, Subgroup.mem_subgroupOf.mp hm, by group⟩
  have hV : ∀ v ∈ V₂, v * (r * v * r⁻¹) * (r * r * v * (r * r)⁻¹) ∈ nK T V g := by
    intro v hv
    refine C.V1_le_nK ?_
    rcases hV₂c v hv with hv1 | ⟨c', hc', rfl⟩
    · rw [C.H_V1 hrH hv1, C.H_V1 ((l32nH T V).mul_mem hrH hrH) hv1,
        S.mul_self_V (Subgroup.mem_inf.mp hv1).1, one_mul]
      exact hv1
    · have hcV : c' ∈ V := (Subgroup.mem_inf.mp hc').1
      have hrc := C.H_V1 hrH hc'
      have e1 : r * (a * c') * r⁻¹ = b * c' := by
        rw [show r * (a * c') * r⁻¹ = (r * a * r⁻¹) * (r * c' * r⁻¹) by group, hra, hrc]
      have e2 : r * r * (a * c') * (r * r)⁻¹ = a * b * c' := by
        rw [show r * r * (a * c') * (r * r)⁻¹ = r * (r * (a * c') * r⁻¹) * r⁻¹ by group, e1,
          show r * (b * c') * r⁻¹ = (r * b * r⁻¹) * (r * c' * r⁻¹) by group, hrb, hrc]
      have hcb : c' * b = b * c' := S.comm_V hcV hbV
      have e3 : a * c' * (b * c') * (a * b * c') = c' := by
        calc a * c' * (b * c') * (a * b * c') = a * (c' * b) * c' * (a * b * c') := by group
          _ = a * (b * c') * c' * (a * b * c') := by rw [hcb]
          _ = a * b * (c' * c') * (a * b * c') := by group
          _ = a * b * (a * b) * c' := by rw [S.mul_self_V hcV, mul_one]; group
          _ = c' := by rw [S.mul_self_V (mul_mem haV hbV), one_mul]
      rw [e1, e2, e3]
      exact hc'
  have hLK : ∀ δ ∈ D.img (lOne L (fsuV1 T V)), δ ∈ D.img (kI T V g) → δ = 1 := by
    intro δ hδL hδK
    by_contra hδ1
    apply C.not_lOne_le
    rw [hL₁, Subgroup.zpowers_le]
    rw [hL₁] at hδL
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδL
    have hδ3 : (γ ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hγ3, one_zpow]
    have hoδ : orderOf (γ ^ k) = 3 := orderOf_eq_prime hδ3 hδ1
    have heq : Subgroup.zpowers (γ ^ k) = Subgroup.zpowers γ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers γ k))
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hoδ, hord])
    have hγδ : γ ∈ Subgroup.zpowers (γ ^ k) := heq ▸ Subgroup.mem_zpowers γ
    exact Subgroup.zpowers_le.mpr hδK hγδ
  have hrP : r ∈ Subgroup.centralizer (vP T V c : Set G) := by
    refine X.cent_of_comm hrH fun h' hh' => ?_
    have hx'K := X.conj_x_mem hh'
    have hrx'K : r * (h' * x * h'⁻¹) * r⁻¹ ∈ kI T V g :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_kI hrH) _).mp hx'K
    have hqK : r * (h' * x * h'⁻¹) * r⁻¹ * (h' * x * h'⁻¹)⁻¹ ∈ kI T V g :=
      (kI T V g).mul_mem hrx'K ((kI T V g).inv_mem hx'K)
    refine X.cent_of_hat h64 hqK ?_
    have hqN := L14332.l32nH_le_normalizer_fsuU T V (C.kI_le hqK)
    refine (L14332.rho_eq_one_iff_mem (D := D) (C.kI_le hqK) hqN).mp ?_
    have hx'N := L14332.l32nH_le_normalizer_fsuU T V (C.kI_le hx'K)
    have hρq : D.ρ ⟨_, hqN⟩ = γ * D.ρ ⟨h' * x * h'⁻¹, hx'N⟩ * γ⁻¹ *
        (D.ρ ⟨h' * x * h'⁻¹, hx'N⟩)⁻¹ := by
      have e1 : (⟨r * (h' * x * h'⁻¹) * r⁻¹ * (h' * x * h'⁻¹)⁻¹, hqN⟩ :
          ↥(Subgroup.normalizer (fsuU T V : Set G))) =
          ⟨r, hrN⟩ * ⟨h' * x * h'⁻¹, hx'N⟩ * ⟨r, hrN⟩⁻¹ * ⟨h' * x * h'⁻¹, hx'N⟩⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, ← hγ]
    rw [hρq]
    have hκK := L128A.HatU.rho_mem_img D hx'K hx'N
    have hκH : D.ρ ⟨h' * x * h'⁻¹, hx'N⟩ ∈ D.img (l32nH T V) :=
      L128A.HatU.rho_mem_img D (C.kI_le hx'K) hx'N
    have hγH : γ ∈ D.img (l32nH T V) := by
      rw [hγ]
      exact L128A.HatU.rho_mem_img D hrH hrN
    refine hLK _ ?_ ?_
    · have h1 := (Subgroup.mem_normalizer_iff.mp (C.l1_normal hκH) _).mp
        ((D.img (lOne L (fsuV1 T V))).inv_mem hγL)
      have h2 := (D.img (lOne L (fsuV1 T V))).mul_mem hγL h1
      have e2 : γ * (D.ρ ⟨h' * x * h'⁻¹, hx'N⟩ * γ⁻¹ * (D.ρ ⟨h' * x * h'⁻¹, hx'N⟩)⁻¹) =
          γ * D.ρ ⟨h' * x * h'⁻¹, hx'N⟩ * γ⁻¹ * (D.ρ ⟨h' * x * h'⁻¹, hx'N⟩)⁻¹ := by group
      rwa [e2] at h2
    · exact (D.img (kI T V g)).mul_mem (C.img_kI_normal hγH hκK)
        ((D.img (kI T V g)).inv_mem hκK)
  have hrc : r * c * r⁻¹ * c⁻¹ = 1 := by
    have := Subgroup.mem_centralizer_iff.mp hrP c (c_mem_vP c)
    calc r * c * r⁻¹ * c⁻¹ = c * r * r⁻¹ * c⁻¹ := by rw [this]
      _ = 1 := by group
  have hcN := mem_of_norm' (N₀ := nK T V g) (V₂ := V₂) C.ctx.U_le
    (L14332.l32nH_le_normalizer_fsuU T V) (fun h hh n hn => conj_mem_nK hh hn)
    (fun u hu v hv => C.V1_le_nK (C.comm u hu v hv)) hU hrH hr3 hxdich hV
    (C.ctx.vH_le X.c_mem).1 (by rw [hrc]; exact one_mem _)
    (by rw [C.vH_sq X.c_mem]; exact one_mem _)
  exact X.c_ne (X.eq_one_of_cent h64 (c_mem_vP c) fun k hk => by
    have := Subgroup.mem_centralizer_iff.mp hcN.2 k hk
    calc k * c * k⁻¹ = c * k * k⁻¹ := by rw [this]
      _ = c := by group)

end CtxI.TransData

theorem Ctx14325.not_case_i (C : Ctx14325 G T L V V₂ g D) (h64 : G64.LemmaG64)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h12810 : Lemma12_8_10) (hd : Module.finrank (ZMod 2) D.V = 4)
    (hi : Case14323i T L V g D) : False := by
  obtain ⟨x, c, X⟩ := (exists_ctxI h1332 h1334 h1222 h12213 h12810 C hd hi).exists_transData
  exact X.false h64 h1332 h1334 h1222 h12213

end L14325

end CFSG.Quasithin.H13
