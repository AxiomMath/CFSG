module

public import CFSG.Quasithin.Vol2.Ch10SecC9S49e
public import CFSG.Quasithin.Vol2.Ch10SecC9S49c
public import CFSG.Quasithin.Vol2.Ch10SecC9S49d
public import CFSG.Quasithin.Vol2.Ch10SecC9S4e

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem odd_card_of_comm {V X : Subgroup G} (hV : IsElemAbelian 2 V) (hred : IsTwoReducedIn X V)
    {A : Subgroup (MulAut (IntMod V hV))} (hA : A ≤ autI hV X)
    (hAn : autI hV X ≤ Subgroup.normalizer (A : Set (MulAut (IntMod V hV))))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Odd (Nat.card ↥A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hzA : (z : MulAut (IntMod V hV)) ∈ pCoreOf 2 A := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (N := Subgroup.zpowers (z : MulAut (IntMod V hV))) ((Subgroup.zpowers_le).mpr z.2)
      (fun n hn => ?_) ?_ (Subgroup.mem_zpowers _)
    · have hcz : n * (z : MulAut (IntMod V hV)) = z * n := hcomm n hn z z.2
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
        rw [(Commute.zpow_right hcz m).eq, mul_inv_cancel_right]
      · intro hy
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
        refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
        have hc' := (Commute.zpow_right hcz m).eq
        calc (z : MulAut (IntMod V hV)) ^ m = n⁻¹ * (n * (z : MulAut (IntMod V hV)) ^ m) := by
              group
          _ = n⁻¹ * ((z : MulAut (IntMod V hV)) ^ m * n) := by rw [hc']
          _ = n⁻¹ * (n * y * n⁻¹) * n := by rw [hm]; group
          _ = y := by group
    · exact IsPGroup.of_card (n := 1)
        (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one])
  have hzQ : (z : MulAut (IntMod V hV)) ∈ pCoreOf 2 (autI hV X) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans hA)
      (hAn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A) hzA
  rw [C1Pack.pCoreOf_autI_eq_bot hV hred, Subgroup.mem_bot] at hzQ
  have := orderOf_one (G := MulAut (IntMod V hV))
  rw [← hzQ, Subgroup.orderOf_coe, hz] at this
  exact absurd this (by norm_num)

namespace Conf

variable {T L I J : Subgroup G} {t w : G} (c : Conf T L I t w J)
include c

theorem thompsonJ_le_centralizer_VI (hVe : IsElemAbelian 2 (VI T L I J w))
    (hXN : J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)) ≤
      Subgroup.normalizer (VI T L I J w : Set G))
    (hIK : autI hVe J ≤ Subgroup.centralizer
      (autI hVe (thompsonJ T) : Set (MulAut (IntMod (VI T L I J w) hVe)))) :
    thompsonJ T ≤ Subgroup.centralizer (VI T L I J w : Set G) := by
  set Tw := T ⊓ Subgroup.centralizer ({w} : Set G)
  have hJT : thompsonJ T ≤ Tw := le_inf (B6.thompsonJ_le T) c.claim.2.2.2.2.1
  intro j hj
  have hjTw := hJT hj
  have hjN : j ∈ Subgroup.normalizer (VI T L I J w : Set G) := hXN (Subgroup.mem_sup_right hjTw)
  suffices hle : VI T L I J w ≤ Subgroup.centralizer ({j} : Set G) by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hv)
  refine conjClosure_le fun h hh z hz => ?_
  have hh' : h ∈ (↑(J ⊔ Tw) : Set G) := hh
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ c.Tw_le_normalizer] at hh'
  obtain ⟨i, hi, s, hs, rfl⟩ := hh'
  have hzs : s * z = z * s := Subgroup.mem_centralizer_iff.mp hz.2 s hs
  have hzV : z ∈ VI T L I J w := le_conjClosure _ _ hz
  have hzj : j * z = z * j := Subgroup.mem_centralizer_iff.mp hz.2 j hjTw
  have hiN : i ∈ Subgroup.normalizer (VI T L I J w : Set G) := hXN (Subgroup.mem_sup_left hi)
  have hcomm := Subgroup.mem_centralizer_iff.mp (hIK (convI_mem_autI hVe hi hiN))
    (convI hVe ⟨j, hjN⟩) (convI_mem_autI hVe hj hjN)
  have hev := congrArg (fun φ : MulAut (IntMod (VI T L I J w) hVe) =>
    (φ (IntMod.mk hVe ⟨z, hzV⟩)).val) hcomm
  simp only [MulAut.mul_apply, convI_apply_val] at hev
  have hev2 : j * (i * z * i⁻¹) * j⁻¹ = i * (j * z * j⁻¹) * i⁻¹ := hev
  have hev' : j * (i * z * i⁻¹) * j⁻¹ = i * z * i⁻¹ := by
    rw [hev2, show j * z * j⁻¹ = z by rw [hzj, mul_inv_cancel_right]]
  have e : i * s * z * (i * s)⁻¹ = i * z * i⁻¹ := by
    rw [mul_inv_rev, show i * s * z * (s⁻¹ * i⁻¹) = i * (s * z * s⁻¹) * i⁻¹ by group, hzs,
      mul_inv_cancel_right]
  rw [e, Subgroup.mem_centralizer_singleton_iff]
  calc i * z * i⁻¹ * j = (j * (i * z * i⁻¹) * j⁻¹) * j := by rw [hev']
    _ = j * (i * z * i⁻¹) := by group

theorem isQuasisimple_autI (h36 : Vol2Native.A36CoreForSQTKCat)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h1026 : Stmt10_2_6)
    (h1027 : Stmt10_2_7) (hK8a : FactK8a) (hK8b : FactK8b)
    (hF : CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))))
    (hVe : IsElemAbelian 2 (VI T L I J w)) : CFSG.Open.IsQuasisimple ↥(autI hVe J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := c.hyp
  set Tw := T ⊓ Subgroup.centralizer ({w} : Set G)
  have hred : IsTwoReducedIn (J ⊔ Tw) (VI T L I J w) :=
    (VI_props hyp c.w_mem_V c.isSylowTwoOf_sup hF).2.2
  have hC := c.centralizer_VI_le h37 h38 h1011 h1026 h1027 hK8a hK8b
  have hXN := hred.2.1
  have hJN : J ≤ Subgroup.normalizer (VI T L I J w : Set G) := le_sup_left.trans hXN
  have hJC : ¬ J ≤ Subgroup.centralizer (VI T L I J w : Set G) := fun h =>
    c.L_not_le_centralizer hC (c.le.trans h)
  by_cases hcen : autI hVe (solvRad J) ≤
      Subgroup.centralizer (autI hVe J : Set (MulAut (IntMod (VI T L I J w) hVe)))
  · exact isQuasisimple_autI_of_central hVe c.mem hJN hJC hcen
  exfalso
  have hJT : thompsonJ T ≤ Tw := le_inf (B6.thompsonJ_le T) c.claim.2.2.2.2.1
  have hJeq : thompsonJ Tw = thompsonJ T := B6.thompsonJ_eq_of_le hJT inf_le_left
  have hK : autI hVe (thompsonJ T) ≤ ffJ (autI hVe (J ⊔ Tw)) :=
    hJeq ▸ autI_thompsonJ_le_ffJ hVe hred c.isSylowTwoOf_sup
  have hJTN : thompsonJ T ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    hJT.trans (le_sup_right.trans hXN)
  have hK2 : IsPGroup 2 ↥(autI hVe (thompsonJ T)) := by
    rw [← range_convHom hVe _ hJTN]
    exact (hyp.fsu.sylow.1.to_le (B6.thompsonJ_le T)).of_surjective _
      (convHom hVe _ hJTN).rangeRestrict_surjective
  have hRX : solvRad J ≤ J ⊔ Tw := (solvRad_le J).trans le_sup_left
  have hRn : J ⊔ Tw ≤ Subgroup.normalizer (solvRad J : Set G) :=
    sup_le (Subgroup.le_normalizer.trans (normalizer_le_normalizer_solvRad J))
      (c.Tw_le_normalizer.trans (normalizer_le_normalizer_solvRad J))
  have h3 := c.not_three_dvd_autI_solvRad h36 hF hVe hcen
  have hKR := autI_le_centralizer_of_three hVe hred hRX hRn (solvRad_isSolvable J) h3 hK hK2
  set Rs := autI hVe (solvRad J)
  set Is := autI hVe J
  set Ks := autI hVe (thompsonJ T)
  have hIRN : Is ≤ Subgroup.normalizer (Rs : Set (MulAut (IntMod (VI T L I J w) hVe))) :=
    autI_le_normalizer_autI hVe (Subgroup.le_normalizer.trans (normalizer_le_normalizer_solvRad J))
  have hCIR : Is ⊓ Subgroup.centralizer (Rs : Set (MulAut (IntMod (VI T L I J w) hVe))) ≤ Rs := by
    set ψ := convHom hVe J hJN
    have hrange : ψ.range = Is := range_convHom hVe J hJN
    set D : Subgroup ↥J :=
      (Subgroup.centralizer (Rs : Set (MulAut (IntMod (VI T L I J w) hVe)))).comap ψ
    have hDn : D.Normal := ⟨fun x hx g => by
      show ψ (g * x * g⁻¹) ∈ Subgroup.centralizer (Rs : Set (MulAut (IntMod (VI T L I J w) hVe)))
      rw [map_mul, map_mul, map_inv]
      have hg : ψ g ∈ Is := hrange ▸ ⟨g, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer' (hIRN hg)) _).mp hx⟩
    rcases normal_eq_top_or_map_le_solvRad c.mem D with h | h
    · exfalso
      apply hcen
      rw [← Subgroup.le_centralizer_iff]
      intro φ hφ
      rw [← hrange] at hφ
      obtain ⟨j, rfl⟩ := hφ
      have : j ∈ D := h ▸ Subgroup.mem_top j
      exact this
    · rintro φ ⟨hφ, hφC⟩
      have hφ' : φ ∈ ψ.range := hrange ▸ hφ
      clear hφ
      rw [MonoidHom.mem_range] at hφ'
      obtain ⟨j, rfl⟩ := hφ'
      have hjR : (j : G) ∈ solvRad J := h ⟨j, hφC, rfl⟩
      exact convI_mem_autI hVe hjR (hJN j.2)
  have hHsN : autI hVe (J ⊔ Tw) ≤
      Subgroup.normalizer (Rs : Set (MulAut (IntMod (VI T L I J w) hVe))) :=
    autI_le_normalizer_autI hVe hRn
  have hHsI : autI hVe (J ⊔ Tw) ≤
      Subgroup.normalizer (Is : Set (MulAut (IntMod (VI T L I J w) hVe))) :=
    autI_le_normalizer_autI hVe (sup_le Subgroup.le_normalizer c.Tw_le_normalizer)
  have hIK : Is ≤ Subgroup.centralizer (Ks : Set (MulAut (IntMod (VI T L I J w) hVe))) := by
    set A := Rs ⊓ Subgroup.centralizer (Rs : Set (MulAut (IntMod (VI T L I J w) hVe)))
    have hAodd : Odd (Nat.card ↥A) :=
      odd_card_of_comm hVe hred (inf_le_left.trans (autI_mono hVe hRX))
        (fun x hx => mem_normalizer_inf' (hHsN hx) (mem_normalizer_centralizer' (hHsN hx)))
        (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb.2 a ha.1)
    intro x hx
    have hxHs : x ∈ autI hVe (J ⊔ Tw) := autI_mono hVe le_sup_left hx
    have hkey : ∀ k ∈ Ks, x * k * x⁻¹ * k⁻¹ ∈ A := by
      intro k hk
      have hkHs : k ∈ autI hVe (J ⊔ Tw) := autI_mono hVe (hJT.trans le_sup_right) hk
      have hcen' : x * k * x⁻¹ * k⁻¹ ∈
          Subgroup.centralizer (Rs : Set (MulAut (IntMod (VI T L I J w) hVe))) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have hr' : x⁻¹ * r * x ∈ Rs := by
          have := (Subgroup.mem_normalizer_iff.mp (hHsN (Subgroup.inv_mem _ hxHs)) r).mp hr
          rwa [inv_inv] at this
        have h1 : k * (x⁻¹ * r * x) = (x⁻¹ * r * x) * k :=
          (Subgroup.mem_centralizer_iff.mp (hKR hr') k hk)
        have h2 : k * r = r * k := Subgroup.mem_centralizer_iff.mp (hKR hr) k hk
        have h3 : r * k⁻¹ = k⁻¹ * r := by
          calc r * k⁻¹ = k⁻¹ * (k * r) * k⁻¹ := by group
            _ = k⁻¹ * (r * k) * k⁻¹ := by rw [h2]
            _ = k⁻¹ * r := by group
        calc r * (x * k * x⁻¹ * k⁻¹) = x * ((x⁻¹ * r * x) * k) * x⁻¹ * k⁻¹ := by group
          _ = x * (k * (x⁻¹ * r * x)) * x⁻¹ * k⁻¹ := by rw [h1]
          _ = x * k * x⁻¹ * (r * k⁻¹) := by group
          _ = x * k * x⁻¹ * (k⁻¹ * r) := by rw [h3]
          _ = x * k * x⁻¹ * k⁻¹ * r := by group
      have hmemI : x * k * x⁻¹ * k⁻¹ ∈ Is := by
        have := (Subgroup.mem_normalizer_iff.mp (hHsI hkHs) x⁻¹).mp (Subgroup.inv_mem _ hx)
        rw [show x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) by group]
        exact Subgroup.mul_mem _ hx this
      exact ⟨hCIR ⟨hmemI, hcen'⟩, hcen'⟩
    have h1 := commutator_eq_one_of_odd hK2 hAodd (inf_le_left.trans hKR) hkey
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h2 : x * k * x⁻¹ = k := by rw [← mul_inv_eq_one]; exact h1 k hk
    calc k * x = (x * k * x⁻¹) * x := by rw [h2]
      _ = x * k := by group
  exact c.not_thompsonJ_le_centralizer h37 h38 h1026 hC
    (c.thompsonJ_le_centralizer_VI hVe hXN hIK)

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC
