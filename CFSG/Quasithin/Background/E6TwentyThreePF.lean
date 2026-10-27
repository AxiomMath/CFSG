module

public import CFSG.Quasithin.Background.E6TwentyThreePA
public import CFSG.Quasithin.Background.E6TwentyThreePE
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.Recognition.HSMultiplierCert

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

section Cover

variable {G : Type} [Group G] {Y : Subgroup G} {Q : Type*} [Group Q] (π : ↥Y →* Q)
  (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center ↥Y)

theorem conj_mul_inv_mem_center (n : ↥(Subgroup.normalizer (Y : Set G))) {y : ↥Y}
    (hy : quotAction π hπ hker n (π y) = π y) :
    Y.normalizerMonoidHom n y * y⁻¹ ∈ Subgroup.center ↥Y := by
  rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, ← quotAction_apply π hπ hker n y _
    (Subgroup.normalizerMonoidHom_apply_apply_coe Y n y), hy, mul_inv_cancel]

theorem card_centralizer_cover [Finite G] (n : ↥(Subgroup.normalizer (Y : Set G)))
    (F : Subgroup Q) (hF : ∀ q, q ∈ F ↔ quotAction π hπ hker n q = q) :
    ∃ d, d ∣ Nat.card ↥(Subgroup.center ↥Y) ∧
      Nat.card ↥(Y ⊓ Subgroup.centralizer ({(n : G)} : Set G)) * d =
        Nat.card ↥(Subgroup.center ↥Y) * Nat.card F := by
  classical
  set W : Subgroup ↥Y := F.comap π with hW
  have hWmem : ∀ w : ↥W, quotAction π hπ hker n (π w) = π w := fun w => (hF _).1 w.2
  let κ : ↥W →* ↥(Subgroup.center ↥Y) := MonoidHom.mk' (fun w =>
      ⟨Y.normalizerMonoidHom n w * (w : ↥Y)⁻¹, conj_mul_inv_mem_center π hπ hker n (hWmem w)⟩)
    (by
      intro w₁ w₂
      apply Subtype.ext
      have hz := Subgroup.mem_center_iff.1 (conj_mul_inv_mem_center π hπ hker n (hWmem w₂))
      show Y.normalizerMonoidHom n ((w₁ * w₂ : ↥W) : ↥Y) * ((w₁ * w₂ : ↥W) : ↥Y)⁻¹ =
        (Y.normalizerMonoidHom n w₁ * (w₁ : ↥Y)⁻¹) * (Y.normalizerMonoidHom n w₂ * (w₂ : ↥Y)⁻¹)
      rw [Subgroup.coe_mul, map_mul, mul_inv_rev]
      calc Y.normalizerMonoidHom n w₁ * Y.normalizerMonoidHom n w₂ *
            ((w₂ : ↥Y)⁻¹ * (w₁ : ↥Y)⁻¹)
          = Y.normalizerMonoidHom n w₁ *
              ((Y.normalizerMonoidHom n w₂ * (w₂ : ↥Y)⁻¹) * (w₁ : ↥Y)⁻¹) := by group
        _ = Y.normalizerMonoidHom n w₁ *
              ((w₁ : ↥Y)⁻¹ * (Y.normalizerMonoidHom n w₂ * (w₂ : ↥Y)⁻¹)) := by
            rw [(hz (w₁ : ↥Y)⁻¹).symm]
        _ = Y.normalizerMonoidHom n w₁ * (w₁ : ↥Y)⁻¹ *
              (Y.normalizerMonoidHom n w₂ * (w₂ : ↥Y)⁻¹) := by group)
  have hkerκ : ∀ w : ↥W,
      w ∈ κ.ker ↔ ((w : ↥Y) : G) ∈ Subgroup.centralizer ({(n : G)} : Set G) := by
    intro w
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1
      have h2 : Y.normalizerMonoidHom n w * (w : ↥Y)⁻¹ = 1 := congrArg Subtype.val h1
      have h3 := congrArg Subtype.val (mul_inv_eq_one.1 h2)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
      calc ((w : ↥Y) : G) * n = ((n : G) * w * (n : G)⁻¹) * n := by rw [h3]
        _ = n * w := by group
    · intro h1
      apply Subtype.ext
      show Y.normalizerMonoidHom n w * (w : ↥Y)⁻¹ = 1
      rw [mul_inv_eq_one]
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ← h1]
      group
  have hCW : ∀ x : ↥(Y ⊓ Subgroup.centralizer ({(n : G)} : Set G)), (⟨x, x.2.1⟩ : ↥Y) ∈ W := by
    intro x
    show π ⟨x, x.2.1⟩ ∈ F
    rw [hF]
    apply quotAction_apply
    have hx : (x : G) * n = n * x := Subgroup.mem_centralizer_singleton_iff.1 x.2.2
    show (x : G) = n * x * (n : G)⁻¹
    rw [← hx]
    group
  have hcardK : Nat.card κ.ker = Nat.card ↥(Y ⊓ Subgroup.centralizer ({(n : G)} : Set G)) :=
    Nat.card_congr
      { toFun := fun k => ⟨((k.1 : ↥Y) : G), (k.1 : ↥Y).2, (hkerκ k.1).1 k.2⟩
        invFun := fun x => ⟨⟨⟨x, x.2.1⟩, hCW x⟩, (hkerκ ⟨⟨x, x.2.1⟩, hCW x⟩).2 x.2.2⟩
        left_inv := fun k => rfl
        right_inv := fun x => rfl }
  have h1 : Nat.card κ.ker * Nat.card κ.range = Nat.card W := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  set f : ↥W →* Q := π.comp W.subtype with hf
  have hfrange : f.range = F := by
    ext q
    constructor
    · rintro ⟨w, rfl⟩
      exact w.2
    · intro hq
      obtain ⟨y, rfl⟩ := hπ q
      exact ⟨⟨y, hq⟩, rfl⟩
  have hkerW : ∀ y : ↥Y, y ∈ π.ker → y ∈ W := fun y hy => by
    show π y ∈ F
    rw [MonoidHom.mem_ker.1 hy]
    exact F.one_mem
  have hfker : Nat.card f.ker = Nat.card π.ker :=
    Nat.card_congr
      { toFun := fun k => ⟨(k.1 : ↥Y), MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 k.2)⟩
        invFun := fun y => ⟨⟨y.1, hkerW y.1 y.2⟩, MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 y.2)⟩
        left_inv := fun k => rfl
        right_inv := fun y => rfl }
  have h2 : Nat.card f.ker * Nat.card f.range = Nat.card W := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hfrange, hfker, hker] at h2
  refine ⟨Nat.card κ.range, Subgroup.card_subgroup_dvd_card κ.range, ?_⟩
  rw [← hcardK, h1, ← h2]

theorem card_fix_dvd_card_centralizer [Finite G] (n : ↥(Subgroup.normalizer (Y : Set G)))
    (F : Subgroup Q) (hF : ∀ q, q ∈ F ↔ quotAction π hπ hker n q = q) :
    Nat.card F ∣ Nat.card ↥(Y ⊓ Subgroup.centralizer ({(n : G)} : Set G)) := by
  obtain ⟨d, ⟨e, he⟩, h⟩ := card_centralizer_cover π hπ hker n F hF
  have hd : 0 < d := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at he
    exact Nat.card_pos.ne' he
  have h' : d * Nat.card ↥(Y ⊓ Subgroup.centralizer ({(n : G)} : Set G)) =
      d * (Nat.card F * e) := by
    rw [mul_comm d, h, he]
    ring
  exact ⟨e, Nat.eq_of_mul_eq_mul_left hd h'⟩

theorem card_centralizer_dvd_cover [Finite G] (n : ↥(Subgroup.normalizer (Y : Set G)))
    (F : Subgroup Q) (hF : ∀ q, q ∈ F ↔ quotAction π hπ hker n q = q) :
    Nat.card ↥(Y ⊓ Subgroup.centralizer ({(n : G)} : Set G)) ∣
      Nat.card ↥(Subgroup.center ↥Y) * Nat.card F := by
  obtain ⟨d, -, h⟩ := card_centralizer_cover π hπ hker n F hF
  exact ⟨d, h.symm⟩

end Cover

private theorem exists_mem_not_mem_finset {M : Type*} [Group M] (H : Subgroup M) (S : Finset M)
    (hS : S.card < Nat.card H) : ∃ x ∈ H, x ∉ S := by
  classical
  by_contra hall
  push Not at hall
  have hsub : (H : Set M) ⊆ ↑S := fun x hx => hall x hx
  have h1 : Nat.card H ≤ S.card :=
    (Nat.card_mono S.finite_toSet hsub).trans_eq (Nat.card_eq_finsetCard S)
  omega

namespace InspHyp

variable {G : Type} [Group G] [Finite G] {Y E X : Subgroup G} {a z : G}

open Equiv CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Quasithin.E6.HSInsp

theorem false_of_patHS
    (h : InspHyp Y E X a z) (hHS : Id2519.PatHS Y X a)
    (h8 : (E ⊓ Subgroup.centralizer (Y : Set G)).relIndex E = 8) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨e⟩, hind⟩ := hHS
  have hperf : Group.IsPerfect ↥Y := h.quasi.1
  have hZ : Nat.card ↥(Subgroup.center ↥Y) ∣ 2 := by
    have h2 := CFSG.Sporadic.Recognition.HSMultiplier.card_center_le_two_of_certificate hperf e
    have h1 : 0 < Nat.card ↥(Subgroup.center ↥Y) := Nat.card_pos
    interval_cases Nat.card ↥(Subgroup.center ↥Y) <;> norm_num
  let θ : (↥Y ⧸ Subgroup.center ↥Y) ≃* ↥hsP := e.trans hsPermEquiv
  let π : ↥Y →* ↥hsP := Id2519.Tab.quotProj θ
  have hπ : Function.Surjective π := Id2519.Tab.quotProj_surjective θ
  have hker : π.ker = Subgroup.center ↥Y := Id2519.Tab.quotProj_ker θ
  obtain ⟨eR, heR, -, -, -⟩ := hs_full_automorphism_model
  obtain ⟨-, -, -, -, hCP, -, -⟩ := hs_normalizing_model
  have hPR : hsP ≤ hsR := le_sup_left (a := hsP) (b := Subgroup.zpowers hsU)
  let ν : ↥(Subgroup.normalizer (Y : Set G)) →* ↥hsR :=
    eR.symm.toMonoidHom.comp (quotAction π hπ hker)
  have hνψ : ∀ (n : ↥(Subgroup.normalizer (Y : Set G))) (p : ↥hsP),
      ((quotAction π hπ hker n p : ↥hsP) : Perm (Fin 3850)) =
        (ν n : Perm (Fin 3850)) * p * (ν n : Perm (Fin 3850))⁻¹ := by
    intro n p
    have h1 : quotAction π hπ hker n = eR (ν n) := by simp [ν]
    rw [h1]
    exact heR (ν n) p
  have hν1 : ∀ n : ↥(Subgroup.normalizer (Y : Set G)),
      ν n = 1 ↔ (n : G) ∈ Subgroup.centralizer (Y : Set G) := by
    intro n
    rw [← quotAction_eq_one_iff π hπ hker hperf n]
    constructor
    · intro h1
      refine MulEquiv.ext fun p => Subtype.ext ?_
      have h2 := hνψ n p
      rw [h1] at h2
      simpa using h2
    · intro h1
      have hc : (ν n : Perm (Fin 3850)) ∈
          Subgroup.centralizer (hsP : Set (Perm (Fin 3850))) := by
        rw [Subgroup.mem_centralizer_iff]
        intro p hp
        have h2 : p = (ν n : Perm (Fin 3850)) * p * (ν n : Perm (Fin 3850))⁻¹ := by
          have h3 := hνψ n ⟨p, hp⟩
          rw [h1] at h3
          exact h3
        calc p * (ν n : Perm (Fin 3850)) =
            ((ν n : Perm (Fin 3850)) * p * (ν n : Perm (Fin 3850))⁻¹) * ν n := by rw [← h2]
          _ = ν n * p := by group
      rw [hCP, Subgroup.mem_bot] at hc
      exact Subtype.ext hc
  have hfixF : ∀ (n : ↥(Subgroup.normalizer (Y : Set G))) (q : ↥hsP),
      q ∈ (hsP ⊓ Subgroup.centralizer ({(ν n : Perm (Fin 3850))} :
        Set (Perm (Fin 3850)))).subgroupOf hsP ↔ quotAction π hπ hker n q = q := by
    intro n q
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h1⟩
      apply Subtype.ext
      rw [hνψ, ← h1]
      group
    · intro h1
      refine ⟨q.2, ?_⟩
      have h2 := congrArg Subtype.val h1
      rw [hνψ] at h2
      calc (q : Perm (Fin 3850)) * ν n =
          ((ν n : Perm (Fin 3850)) * q * (ν n : Perm (Fin 3850))⁻¹) * ν n := by rw [h2]
        _ = ν n * q := by group
  have hcov : ∀ n : ↥(Subgroup.normalizer (Y : Set G)),
      Nat.card ↥(hsP ⊓ Subgroup.centralizer ({(ν n : Perm (Fin 3850))} :
          Set (Perm (Fin 3850)))) ∣ Nat.card ↥(Y ⊓ Subgroup.centralizer ({(n : G)} : Set G)) ∧
        Nat.card ↥(Y ⊓ Subgroup.centralizer ({(n : G)} : Set G)) ∣
          2 * Nat.card ↥(hsP ⊓ Subgroup.centralizer ({(ν n : Perm (Fin 3850))} :
            Set (Perm (Fin 3850)))) := by
    intro n
    have hc := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : hsP ⊓
      Subgroup.centralizer ({(ν n : Perm (Fin 3850))} : Set (Perm (Fin 3850))) ≤ hsP)).toEquiv
    have h1 := card_fix_dvd_card_centralizer π hπ hker n _ (hfixF n)
    have h2 := card_centralizer_dvd_cover π hπ hker n _ (hfixF n)
    rw [hc] at h1 h2
    exact ⟨h1, h2.trans (mul_dvd_mul_right hZ _)⟩
  have hcardE : Nat.card ↥((E.subgroupOf (Subgroup.normalizer (Y : Set G))).map ν) = 8 := by
    have h1 := card_map_quotAction π hπ hker hperf h.norm
    rw [h8] at h1
    have h2 : (E.subgroupOf (Subgroup.normalizer (Y : Set G))).map ν =
        ((E.subgroupOf (Subgroup.normalizer (Y : Set G))).map (quotAction π hπ hker)).map
          eR.symm.toMonoidHom := (Subgroup.map_map _ _ _).symm
    rw [h2, Subgroup.card_map_of_injective eR.symm.injective, h1]
  set V : Subgroup (Perm (Fin 3850)) :=
    ((E.subgroupOf (Subgroup.normalizer (Y : Set G))).map ν).map hsR.subtype with hV
  have hcardV : Nat.card V = 8 := by
    rw [hV, Subgroup.card_map_of_injective hsR.subtype_injective, hcardE]
  have hVmem : ∀ x ∈ V, ∃ b : ↥(Subgroup.normalizer (Y : Set G)), (b : G) ∈ E ∧
      (ν b : Perm (Fin 3850)) = x := by
    intro x hx
    rw [hV] at hx
    obtain ⟨r, ⟨b, hb, rfl⟩, rfl⟩ := hx
    exact ⟨b, hb, rfl⟩
  have hνmem : ∀ b : ↥(Subgroup.normalizer (Y : Set G)), (b : G) ∈ E →
      (ν b : Perm (Fin 3850)) ∈ V := fun b hb => by
    rw [hV]
    exact ⟨ν b, ⟨b, hb, rfl⟩, rfl⟩
  have hVR : V ≤ hsR := Subgroup.map_subtype_le _
  have hVsq : ∀ x ∈ V, x * x = 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := hVmem x hx
    have hb2 : b * b = 1 := Subtype.ext (h.mul_self_eq_one hb)
    have h1 : ν b * ν b = 1 := by rw [← map_mul, hb2, map_one]
    exact congrArg Subtype.val h1
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    obtain ⟨b, hb, rfl⟩ := hVmem x hx
    obtain ⟨c, hc, rfl⟩ := hVmem y hy
    have hbc : b * c = c * b := Subtype.ext (h.mul_comm_of_mem hb hc)
    have h1 : ν b * ν c = ν c * ν b := by rw [← map_mul, hbc, map_mul]
    exact congrArg Subtype.val h1
  have haN : a ∈ Subgroup.normalizer (Y : Set G) := h.norm h.mem
  obtain ⟨hh, hhdef⟩ : ∃ hh : Perm (Fin 3850),
      (ν ⟨a, haN⟩ : Perm (Fin 3850)) = hh := ⟨_, rfl⟩
  have hhV : hh ∈ V := hhdef ▸ hνmem ⟨a, haN⟩ h.mem
  have hhR : hh ∈ hsR := hVR hhV
  have hh1 : hh ≠ 1 := by
    intro h1
    have h2 : ν ⟨a, haN⟩ = 1 := Subtype.ext (hhdef.trans h1)
    rw [hν1] at h2
    exact h.not_cent fun y hy => Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 h2 y hy)
  have hhP : hh ∈ hsP := by
    obtain ⟨l, hl, hlt⟩ := hind
    have hconj : ∀ y : ↥Y, ((Y.normalizerMonoidHom ⟨a, haN⟩ y : ↥Y) : G) = l * y * l⁻¹ := by
      intro y
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hy' : a * (y : G) * a⁻¹ ∈ Y := by
        have := (Y.normalizerMonoidHom ⟨a, haN⟩ y).2
        rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at this
      have h1 := hlt _ hy'
      have e1 : a⁻¹ * (a * (y : G) * a⁻¹) * a = y := by group
      rw [e1] at h1
      show a * (y : G) * a⁻¹ = l * y * l⁻¹
      calc a * (y : G) * a⁻¹ = l * (l⁻¹ * (a * y * a⁻¹) * l) * l⁻¹ := by group
        _ = l * y * l⁻¹ := by rw [← h1]
    have hq : ∀ p : ↥hsP, quotAction π hπ hker ⟨a, haN⟩ p = π ⟨l, hl⟩ * p * (π ⟨l, hl⟩)⁻¹ := by
      intro p
      obtain ⟨y, rfl⟩ := hπ p
      rw [quotAction_apply π hπ hker ⟨a, haN⟩ y (Y.normalizerMonoidHom ⟨a, haN⟩ y)
        (Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨a, haN⟩ y)]
      have h1 : Y.normalizerMonoidHom ⟨a, haN⟩ y = ⟨l, hl⟩ * y * (⟨l, hl⟩ : ↥Y)⁻¹ :=
        Subtype.ext (by rw [hconj]; rfl)
      rw [h1, map_mul, map_mul, map_inv]
    have hc : hh⁻¹ * ((π ⟨l, hl⟩ : ↥hsP) : Perm (Fin 3850)) ∈
        Subgroup.centralizer (hsP : Set (Perm (Fin 3850))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have h1 := hνψ ⟨a, haN⟩ ⟨p, hp⟩
      rw [hq, hhdef] at h1
      have h2 : ((π ⟨l, hl⟩ : ↥hsP) : Perm (Fin 3850)) * p *
          ((π ⟨l, hl⟩ : ↥hsP) : Perm (Fin 3850))⁻¹ = hh * p * hh⁻¹ := h1
      calc p * (hh⁻¹ * ((π ⟨l, hl⟩ : ↥hsP) : Perm (Fin 3850))) =
          hh⁻¹ * (hh * p * hh⁻¹) * ((π ⟨l, hl⟩ : ↥hsP) : Perm (Fin 3850)) := by group
        _ = hh⁻¹ * (((π ⟨l, hl⟩ : ↥hsP) : Perm (Fin 3850)) * p *
              ((π ⟨l, hl⟩ : ↥hsP) : Perm (Fin 3850))⁻¹) *
            ((π ⟨l, hl⟩ : ↥hsP) : Perm (Fin 3850)) := by rw [h2]
        _ = hh⁻¹ * ((π ⟨l, hl⟩ : ↥hsP) : Perm (Fin 3850)) * p := by group
    rw [hCP, Subgroup.mem_bot] at hc
    rw [inv_mul_eq_one.1 hc]
    exact (π ⟨l, hl⟩).2
  have h360 : 360 ∣ Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G)) := by
    rw [← h.card_X]
    exact Subgroup.card_dvd_of_le h.comp.1
  have hcova := hcov ⟨a, haN⟩
  rw [hhdef] at hcova
  have hh2 : hh * hh = 1 := hVsq hh hhV
  obtain ⟨g, hgP, hhg⟩ : ∃ g ∈ hsP, hh = g * hsT2 * g⁻¹ := by
    rcases involution_cases hhR hh2 hh1 with h1 | ⟨-, h7680⟩ | ⟨hnP, -⟩
    · exact h1
    · exfalso
      have h2 := hcova.2
      rw [h7680] at h2
      have h3 := h360.trans h2
      norm_num at h3
    · exact absurd hhP hnP
  have hCh : Nat.card ↥(hsP ⊓ Subgroup.centralizer ({hh} : Set (Perm (Fin 3850)))) = 2880 := by
    rw [hhg, inf_centralizer_conj hsP hgP, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact card_C2
  have ht0P : hsT2 ∈ hsP := by
    have h1 := hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hgP) hhP) hgP
    rwa [hhg, show g⁻¹ * (g * hsT2 * g⁻¹) * g = hsT2 by group] at h1
  obtain ⟨T, hT, hET⟩ := h.exists_sylow_a
  have hTY : T ≤ Y := hT.le.trans inf_le_left
  set TP : Subgroup (Perm (Fin 3850)) := ((T.subgroupOf Y).map π).map hsP.subtype with hTP
  have hTPmem : ∀ x ∈ TP, ∃ t : ↥Y, (t : G) ∈ T ∧ ((π t : ↥hsP) : Perm (Fin 3850)) = x := by
    intro x hx
    rw [hTP] at hx
    obtain ⟨q, ⟨t, ht, rfl⟩, rfl⟩ := hx
    exact ⟨t, ht, rfl⟩
  have hfixT : ∀ (n : ↥(Subgroup.normalizer (Y : Set G))) (t : ↥Y), (t : G) * n = n * t →
      (ν n : Perm (Fin 3850)) * (π t : Perm (Fin 3850)) =
        (π t : Perm (Fin 3850)) * (ν n : Perm (Fin 3850)) := by
    intro n t htn
    have h1 : Y.normalizerMonoidHom n t = t := Subtype.ext (by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ← htn]
      group)
    have h2 := hνψ n (π t)
    rw [quotAction_apply π hπ hker n t _ (Subgroup.normalizerMonoidHom_apply_apply_coe Y n t),
      h1] at h2
    calc (ν n : Perm (Fin 3850)) * (π t : Perm (Fin 3850)) =
        ((ν n : Perm (Fin 3850)) * (π t : Perm (Fin 3850)) * (ν n : Perm (Fin 3850))⁻¹) *
          ν n := by group
      _ = (π t : Perm (Fin 3850)) * ν n := by rw [← h2]
  have hTPC : TP ≤ hsP ⊓ Subgroup.centralizer ({hh} : Set (Perm (Fin 3850))) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hTPmem x hx
    refine ⟨(π t).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hta : (t : G) * a = a * t := Subgroup.mem_centralizer_singleton_iff.1 (hT.le ht).2
    have h1 := hfixT ⟨a, haN⟩ t hta
    rw [hhdef] at h1
    exact h1.symm
  have hVTP : ∀ x ∈ V, ∀ y ∈ TP, x * y = y * x := by
    intro x hx y hy
    obtain ⟨b, hb, rfl⟩ := hVmem x hx
    obtain ⟨t, ht, rfl⟩ := hTPmem y hy
    exact hfixT b t (Subgroup.mem_centralizer_iff.1 (hET hb) t ht)
  have hTP2 : IsPGroup 2 TP := by
    have h1 : IsPGroup 2 (T.subgroupOf Y) :=
      hT.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hTY).symm
    exact (h1.map π).map hsP.subtype
  have hcardT : Nat.card T ∣ 2 * Nat.card TP := by
    set f : ↥(T.subgroupOf Y) →* ↥hsP := π.comp (T.subgroupOf Y).subtype with hf
    have hrange : f.range = (T.subgroupOf Y).map π := by
      rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 : Nat.card f.ker * Nat.card f.range = Nat.card ↥(T.subgroupOf Y) := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    have hk : Nat.card f.ker ∣ 2 := by
      have hle : Nat.card f.ker ≤ Nat.card ↥(Subgroup.center ↥Y) := by
        rw [← hker]
        refine Nat.card_le_card_of_injective
          (fun k => ⟨(k.1 : ↥Y), MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 k.2)⟩) ?_
        intro k k' hkk
        exact Subtype.ext (Subtype.ext (Subtype.ext
          (congrArg (fun w : ↥π.ker => ((w : ↥Y) : G)) hkk)))
      have hZ2 : Nat.card ↥(Subgroup.center ↥Y) ≤ 2 := Nat.le_of_dvd (by norm_num) hZ
      have hle2 : Nat.card f.ker ≤ 2 := hle.trans hZ2
      have hpos : 0 < Nat.card f.ker := Nat.card_pos
      interval_cases Nat.card f.ker <;> norm_num
    have hTT : Nat.card T = Nat.card ↥(T.subgroupOf Y) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv).symm
    have hTPc : Nat.card TP = Nat.card ↥((T.subgroupOf Y).map π) :=
      Subgroup.card_map_of_injective hsP.subtype_injective
    rw [hTT, ← h1, hrange, hTPc]
    exact mul_dvd_mul_right hk _
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hTP2
  have hj6 : j ≤ 6 := by
    have hdvd : Nat.card TP ∣ 2880 := by
      rw [← hCh]
      exact Subgroup.card_dvd_of_le hTPC
    rw [hj] at hdvd
    by_contra hj7
    push Not at hj7
    have h7 : 2 ^ 7 ∣ 2880 := (Nat.pow_dvd_pow 2 hj7).trans hdvd
    norm_num at h7
  by_cases h64 : j = 6
  ·
    have hcard64 : Nat.card TP = 64 := by rw [hj, h64]; norm_num
    set S := TP.map (MulAut.conj g⁻¹).toMonoidHom with hS
    have hSC : S ≤ hsC2 := by
      intro x hx
      rw [hS] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hyC := hTPC hy
      have hyh : y * hh = hh * y := Subgroup.mem_centralizer_singleton_iff.1 hyC.2
      rw [hhg] at hyh
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      refine ⟨hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hgP) hyC.1) hgP,
        Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc g⁻¹ * y * g * hsT2 = g⁻¹ * (y * (g * hsT2 * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * hsT2 * g⁻¹) * y) * g := by rw [hyh]
        _ = hsT2 * (g⁻¹ * y * g) := by group
    have hScard : Nat.card S = 64 := by
      rw [hS, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcard64]
    have hkR : g⁻¹ ∈ hsR := hPR (hsP.inv_mem hgP)
    have hle : V.map (MulAut.conj g⁻¹).toMonoidHom ≤
        hsR ⊓ Subgroup.centralizer (S : Set (Perm (Fin 3850))) := by
      rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine Subgroup.mem_inf.2 ⟨hsR.mul_mem (hsR.mul_mem hkR (hVR hx)) (hsR.inv_mem hkR), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rw [hS] at ht
      obtain ⟨y, hy, rfl⟩ := ht
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hxy := hVTP x hx y hy
      calc _ = g⁻¹ * (y * x) * g⁻¹⁻¹ := by group
        _ = g⁻¹ * (x * y) * g⁻¹⁻¹ := by rw [hxy]
        _ = _ := by group
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcardV] at h1
    have h2 := cent_le_four hSC hScard
    omega
  ·
    have hj5 : j ≤ 5 := by omega
    have hT64 : Nat.card T ∣ 2 ^ 6 := by
      have h1 : Nat.card TP ∣ 2 ^ 5 := by
        rw [hj]
        exact Nat.pow_dvd_pow 2 hj5
      have h2 : (2 : ℕ) ^ 6 = 2 * 2 ^ 5 := by norm_num
      rw [h2]
      exact hcardT.trans (mul_dvd_mul_left 2 h1)
    have hfa : (Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G))).factorization 2 ≤ 6 := by
      rw [hT.card_eq] at hT64
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hT64
    have hpure : ∀ x ∈ V, x ≠ 1 → ∃ g' ∈ hsP, x = g' * hsT2 * g'⁻¹ := by
      intro x hx hx1
      obtain ⟨b, hb, rfl⟩ := hVmem x hx
      have hbY : ¬ Y ≤ Subgroup.centralizer ({(b : G)} : Set G) := by
        intro hle
        apply hx1
        have h1 : ν b = 1 := (hν1 b).2 (Subgroup.mem_centralizer_iff.2 fun y hy =>
          Subgroup.mem_centralizer_singleton_iff.1 (hle hy))
        rw [h1]
        rfl
      have h1 := h.factorization_le hb hbY
      have h2 := (hcov b).1
      have h3 : (Nat.card ↥(hsP ⊓ Subgroup.centralizer ({(ν b : Perm (Fin 3850))} :
          Set (Perm (Fin 3850))))).factorization 2 ≤ 6 := by
        refine le_trans ?_ (h1.trans hfa)
        refine (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 ?_
        exact ((Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 le_rfl).trans h2
      rcases involution_cases (ν b).2 (hVsq _ hx) hx1 with h4 | ⟨-, h4⟩ | ⟨-, h4⟩
      · exact h4
      · exfalso
        rw [h4] at h3
        have h9 : 9 ≤ (7680 : ℕ).factorization 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).1 (by norm_num)
        omega
      · exfalso
        have h7 := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h4
        omega
    have hVconj : ∀ x ∈ V, x ≠ 1 → ∃ g'' ∈ hsP, g⁻¹ * x * g = g'' * hsT2 * g''⁻¹ := by
      intro x hx hx1
      obtain ⟨g', hg', rfl⟩ := hpure x hx hx1
      exact ⟨g⁻¹ * g', hsP.mul_mem (hsP.inv_mem hgP) hg', by group⟩
    have hVP : ∀ x ∈ V, x ≠ 1 → g⁻¹ * x * g ∈ hsP := by
      intro x hx hx1
      obtain ⟨g', hg', rfl⟩ := hpure x hx hx1
      exact hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hgP)
        (hsP.mul_mem (hsP.mul_mem hg' ht0P) (hsP.inv_mem hg'))) hgP
    have ht0 : hsT2 = g⁻¹ * hh * g := by rw [hhg]; group
    have hinj : ∀ x y : Perm (Fin 3850), g⁻¹ * x * g = g⁻¹ * y * g → x = y :=
      fun x y hxy => mul_left_cancel (mul_right_cancel hxy)
    have hinv : ∀ x ∈ V, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hVsq x hx)
    obtain ⟨b, hbV, hbS⟩ := exists_mem_not_mem_finset V ({1, hh} : Finset (Perm (Fin 3850)))
      (by rw [hcardV]; exact lt_of_le_of_lt Finset.card_le_two (by norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbS
    obtain ⟨hb1, hbh⟩ := hbS
    obtain ⟨c, hcV, hcS⟩ := exists_mem_not_mem_finset V
      ({1, hh, b, hh * b} : Finset (Perm (Fin 3850)))
      (by rw [hcardV]; exact lt_of_le_of_lt Finset.card_le_four (by norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcS
    obtain ⟨hc1, hch, hcb, chb⟩ := hcS
    have hbc1 : b * c ≠ 1 := fun h1 => hcb (by rw [eq_inv_of_mul_eq_one_right h1, hinv b hbV])
    have hhb1 : hh * b ≠ 1 := fun h1 => hbh (by rw [eq_inv_of_mul_eq_one_right h1, hinv hh hhV])
    have hhc1 : hh * c ≠ 1 := fun h1 => hch (by rw [eq_inv_of_mul_eq_one_right h1, hinv hh hhV])
    have hhbc1 : hh * (b * c) ≠ 1 := by
      intro h1
      apply chb
      rw [← mul_assoc] at h1
      rw [eq_inv_of_mul_eq_one_right h1, mul_inv_rev, hinv b hbV, hinv hh hhV,
        hVcomm b hbV hh hhV]
    have hbcV : b * c ∈ V := V.mul_mem hbV hcV
    have hbt : b * hh = hh * b := hVcomm b hbV hh hhV
    have hct : c * hh = hh * c := hVcomm c hcV hh hhV
    have hmemC : ∀ x ∈ V, x ≠ 1 → g⁻¹ * x * g ∈ hsC2 := by
      intro x hx hx1
      refine ⟨hVP x hx hx1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [ht0]
      calc g⁻¹ * x * g * (g⁻¹ * hh * g) = g⁻¹ * (x * hh) * g := by group
        _ = g⁻¹ * (hh * x) * g := by rw [hVcomm x hx hh hhV]
        _ = g⁻¹ * hh * g * (g⁻¹ * x * g) := by group
    refine not_pure (b := g⁻¹ * b * g) (c := g⁻¹ * c * g) (hmemC b hbV hb1) (hmemC c hcV hc1)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hVconj b hbV hb1) (hVconj c hcV hc1) ?_ ?_ ?_ ?_
    · intro h1
      exact hb1 (hinj _ _ (by rw [h1]; group))
    · intro h1
      exact hc1 (hinj _ _ (by rw [h1]; group))
    · calc g⁻¹ * b * g * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g := by group
        _ = 1 := by rw [hVsq b hbV]; group
    · calc g⁻¹ * c * g * (g⁻¹ * c * g) = g⁻¹ * (c * c) * g := by group
        _ = 1 := by rw [hVsq c hcV]; group
    · calc g⁻¹ * b * g * (g⁻¹ * c * g) = g⁻¹ * (b * c) * g := by group
        _ = g⁻¹ * (c * b) * g := by rw [hVcomm b hbV c hcV]
        _ = g⁻¹ * c * g * (g⁻¹ * b * g) := by group
    · intro h1
      exact hbh (hinj _ _ (by rw [h1, ht0]))
    · intro h1
      exact hch (hinj _ _ (by rw [h1, ht0]))
    · intro h1
      exact hcb (hinj _ _ h1)
    · intro h1
      exact chb (hinj _ _ (by rw [h1, ht0]; group))
    · rw [show g⁻¹ * b * g * (g⁻¹ * c * g) = g⁻¹ * (b * c) * g by group]
      exact hVconj _ hbcV hbc1
    · have e : hsT2 * (g⁻¹ * b * g) = g⁻¹ * (hh * b) * g := by rw [ht0]; group
      rw [e]
      exact hVconj _ (V.mul_mem hhV hbV) hhb1
    · have e : hsT2 * (g⁻¹ * c * g) = g⁻¹ * (hh * c) * g := by rw [ht0]; group
      rw [e]
      exact hVconj _ (V.mul_mem hhV hcV) hhc1
    · have e : hsT2 * (g⁻¹ * b * g * (g⁻¹ * c * g)) = g⁻¹ * (hh * (b * c)) * g := by
        rw [ht0]; group
      rw [e]
      exact hVconj _ (V.mul_mem hhV hbcV) hhbc1

end InspHyp

end CFSG.Quasithin.E6
