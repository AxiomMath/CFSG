module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CTorus
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC6S846

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5c_rhoL_pow_three {L : Subgroup G} {a : G}
    (haL : a ∈ normalizer (L : Set G)) (ha3 : a ^ 3 = 1) :
    UC6S846.rhoL L ⟨a, haL⟩ ^ 3 = 1 := by
  rw [← map_pow]
  have h1 : (⟨a, haL⟩ : ↥(normalizer (L : Set G))) ^ 3 = 1 := by
    refine Subtype.ext ?_
    simpa using ha3
  rw [h1, map_one]

theorem uc22r3e5c_exists_bar2_conj_link (g : G) (L : Subgroup G) :
    ∃ φ : Bar2 L ≃* Bar2 (L.map (MulAut.conj g).toMonoidHom),
      ∀ (x : ↥L) (hx : g * (x : G) * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom),
        φ (QuotientGroup.mk x) =
          QuotientGroup.mk (⟨g * (x : G) * g⁻¹,
            hx⟩ : ↥(L.map (MulAut.conj g).toMonoidHom)) := by
  let e : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
    { toFun := fun x =>
        ⟨g * (x : G) * g⁻¹, Subgroup.mem_map.2 ⟨x, x.2, by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩⟩
      invFun := fun y =>
        ⟨g⁻¹ * (y : G) * g, by
          obtain ⟨l, hl, hyl⟩ := Subgroup.mem_map.1 y.2
          rw [← hyl]
          show g⁻¹ * (MulAut.conj g) (l : G) * g ∈ L
          rw [MulAut.conj_apply]
          rwa [show g⁻¹ * (g * (l : G) * g⁻¹) * g = (l : G) by group]⟩
      left_inv := fun x => Subtype.ext (by group)
      right_inv := fun y => Subtype.ext (by group)
      map_mul' := fun x y => Subtype.ext (by
        show g * ((x : G) * (y : G)) * g⁻¹ =
          g * (x : G) * g⁻¹ * (g * (y : G) * g⁻¹)
        group) }
  have he : Subgroup.map (↑e) (CFSG.pCore 2 ↥L) =
      CFSG.pCore 2 ↥(L.map (MulAut.conj g).toMonoidHom) :=
    CFSG.pCore_map_iso 2 e
  refine ⟨QuotientGroup.congr (CFSG.pCore 2 ↥L)
    (CFSG.pCore 2 ↥(L.map (MulAut.conj g).toMonoidHom)) e he, fun x hx => ?_⟩
  rw [QuotientGroup.congr_mk]
  congr 1

private theorem uc22r3e5c_conj_inv_elem {b g x : G} (hgb : g * b * g⁻¹ = b⁻¹) :
    b * (g * x * g⁻¹) * b⁻¹ = g * (b⁻¹ * x * b) * g⁻¹ := by
  have hbg : b * g = g * b⁻¹ := by
    have h : g * b⁻¹ * g⁻¹ = b := by
      simpa [mul_assoc] using congrArg (fun z => z⁻¹) hgb
    calc b * g = (g * b⁻¹ * g⁻¹) * g := by rw [h]
      _ = g * b⁻¹ := by group
  have hbg' : g⁻¹ * b⁻¹ = b * g⁻¹ := by
    rw [← mul_inv_rev, hbg, mul_inv_rev, inv_inv]
  rw [show b * (g * x * g⁻¹) * b⁻¹ = (b * g) * x * (g⁻¹ * b⁻¹) by group, hbg, hbg']
  group

theorem uc22r3e5c_rhoL_conj_swap {L : Subgroup G} {b g : G}
    (hgb : g * b * g⁻¹ = b⁻¹) (hbL : b ∈ normalizer (L : Set G))
    (hbK : b ∈ normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
    (φ : Bar2 L ≃* Bar2 (L.map (MulAut.conj g).toMonoidHom))
    (hφ : ∀ (x : ↥L) (hx : g * (x : G) * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom),
      φ (QuotientGroup.mk x) =
        QuotientGroup.mk (⟨g * (x : G) * g⁻¹,
          hx⟩ : ↥(L.map (MulAut.conj g).toMonoidHom)))
    (z : Bar2 L) :
    UC6S846.rhoL (L.map (MulAut.conj g).toMonoidHom) ⟨b, hbK⟩ (φ z) =
      φ ((UC6S846.rhoL L ⟨b, hbL⟩)⁻¹ z) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  have hxK : g * (x : G) * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.2 ⟨x, x.2, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hgroup := uc22r3e5c_conj_inv_elem (x := (x : G)) hgb
  have hbLinv : (⟨b, hbL⟩ : ↥(normalizer (L : Set G)))⁻¹ =
      ⟨b⁻¹, Subgroup.inv_mem _ hbL⟩ := Subtype.ext rfl
  let y : ↥L := Subgroup.normalizerMonoidHom L ⟨b⁻¹, Subgroup.inv_mem _ hbL⟩ x
  have hy : g * (y : G) * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.2 ⟨y, y.2, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hycoe : (y : G) = b⁻¹ * (x : G) * b := by
    show ((Subgroup.normalizerMonoidHom L ⟨b⁻¹, Subgroup.inv_mem _ hbL⟩ x : ↥L) : G) = _
    rw [UC6S846.rhoL_mk_coe]
    simp
  rw [hφ x hxK, ← map_inv (UC6S846.rhoL L) ⟨b, hbL⟩, hbLinv, UC6S846.rhoL_mk]
  rw [UC6S846.rhoL_mk]
  refine (congrArg QuotientGroup.mk (Subtype.ext ?_)).trans (hφ y hy).symm
  change ((Subgroup.normalizerMonoidHom (L.map (MulAut.conj g).toMonoidHom) ⟨b, hbK⟩
    ⟨g * (x : G) * g⁻¹, hxK⟩ : ↥(L.map (MulAut.conj g).toMonoidHom)) : G) =
    g * (y : G) * g⁻¹
  rw [UC6S846.rhoL_mk_coe, hycoe]
  exact hgroup

private theorem uc22r3e5c_rhoL_inv_map_eq {L : Subgroup G} {b : G}
    (hbL : b ∈ normalizer (L : Set G))
    (hαinv : (UC6S846.rhoL L ⟨b, hbL⟩)⁻¹ = UC6S846.rhoL L ⟨b, hbL⟩ ^ 2)
    {H : Subgroup (Bar2 L)}
    (hH : H.map (UC6S846.rhoL L ⟨b, hbL⟩).toMonoidHom = H) :
    H.map ((UC6S846.rhoL L ⟨b, hbL⟩)⁻¹).toMonoidHom = H := by
  rw [hαinv, pow_two]
  show H.map (MonoidHom.comp (UC6S846.rhoL L ⟨b, hbL⟩).toMonoidHom
    (UC6S846.rhoL L ⟨b, hbL⟩).toMonoidHom) = H
  rw [← Subgroup.map_map, hH, hH]

private theorem uc22r3e5c_map_swap {L : Subgroup G} {b g : G}
    (hbL : b ∈ normalizer (L : Set G))
    (hbK : b ∈ normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
    (φ : Bar2 L ≃* Bar2 (L.map (MulAut.conj g).toMonoidHom))
    (hcomp : (UC6S846.rhoL (L.map (MulAut.conj g).toMonoidHom) ⟨b, hbK⟩).toMonoidHom.comp
        φ.toMonoidHom =
      φ.toMonoidHom.comp ((UC6S846.rhoL L ⟨b, hbL⟩)⁻¹).toMonoidHom)
    {H : Subgroup (Bar2 L)}
    (hHinv : H.map ((UC6S846.rhoL L ⟨b, hbL⟩)⁻¹).toMonoidHom = H) :
    (H.map φ.toMonoidHom).map
        (UC6S846.rhoL (L.map (MulAut.conj g).toMonoidHom) ⟨b, hbK⟩).toMonoidHom =
      H.map φ.toMonoidHom := by
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hHinv]

private theorem uc22r3e5c_torusExp_swap_he {L : Subgroup G} {b g : G}
    (hbL : b ∈ normalizer (L : Set G))
    (hbK : b ∈ normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
    (hgb : g * b * g⁻¹ = b⁻¹)
    (hαinv : (UC6S846.rhoL L ⟨b, hbL⟩)⁻¹ = UC6S846.rhoL L ⟨b, hbL⟩ ^ 2)
    {DL : Subgroup (Bar2 L)}
    (hDLα : DL.map (UC6S846.rhoL L ⟨b, hbL⟩).toMonoidHom = DL)
    {e : ℕ} (he : ∀ d ∈ DL, UC6S846.rhoL L ⟨b, hbL⟩ d = d ^ e)
    (φ : Bar2 L ≃* Bar2 (L.map (MulAut.conj g).toMonoidHom))
    (hφ : ∀ (x : ↥L) (hx : g * (x : G) * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom),
      φ (QuotientGroup.mk x) =
        QuotientGroup.mk (⟨g * (x : G) * g⁻¹,
          hx⟩ : ↥(L.map (MulAut.conj g).toMonoidHom))) :
    ∀ c ∈ DL.map φ.toMonoidHom,
      UC6S846.rhoL (L.map (MulAut.conj g).toMonoidHom) ⟨b, hbK⟩ c = c ^ (e * e) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hc
  have hdDL : UC6S846.rhoL L ⟨b, hbL⟩ d ∈ DL := by
    rw [← hDLα]
    exact Subgroup.mem_map_of_mem _ hd
  change UC6S846.rhoL (L.map (MulAut.conj g).toMonoidHom) ⟨b, hbK⟩ (φ d) =
    (φ d) ^ (e * e)
  have h1 : (UC6S846.rhoL L ⟨b, hbL⟩)⁻¹ d = d ^ (e * e) := by
    rw [hαinv, pow_two]
    change UC6S846.rhoL L ⟨b, hbL⟩ (UC6S846.rhoL L ⟨b, hbL⟩ d) = d ^ (e * e)
    rw [he (UC6S846.rhoL L ⟨b, hbL⟩ d) hdDL, he d hd, ← pow_mul]
  rw [uc22r3e5c_rhoL_conj_swap hgb hbL hbK φ hφ d, h1, map_pow]

theorem uc22r3e5c_torusExp_swap {L K : Subgroup G} {b g : G}
    (hbL : b ∈ normalizer (L : Set G)) (hbK : b ∈ normalizer (K : Set G)) (hb3 : b ^ 3 = 1)
    (hgb : g * b * g⁻¹ = b⁻¹) (hLg : L.map (MulAut.conj g).toMonoidHom = K)
    {n : ℕ} (hSzK : IsSz (Bar2 K) n)
    (UL : Sylow 2 (Bar2 L)) {DL : Subgroup (Bar2 L)}
    (hDL : DL ≤ normalizer ((UL : Subgroup (Bar2 L)) : Set (Bar2 L)))
    (hDLc : Nat.card DL = 2 ^ n - 1)
    (hUL : (UL : Subgroup (Bar2 L)).map (UC6S846.rhoL L ⟨b, hbL⟩).toMonoidHom = UL)
    (hDLα : DL.map (UC6S846.rhoL L ⟨b, hbL⟩).toMonoidHom = DL)
    (UK : Sylow 2 (Bar2 K)) {DK : Subgroup (Bar2 K)}
    (hDK : DK ≤ normalizer ((UK : Subgroup (Bar2 K)) : Set (Bar2 K)))
    (hDKc : Nat.card DK = 2 ^ n - 1)
    (hUK : (UK : Subgroup (Bar2 K)).map (UC6S846.rhoL K ⟨b, hbK⟩).toMonoidHom = UK)
    (hDKα : DK.map (UC6S846.rhoL K ⟨b, hbK⟩).toMonoidHom = DK)
    {e : ℕ} (he : ∀ d ∈ DL, UC6S846.rhoL L ⟨b, hbL⟩ d = d ^ e) :
    ∀ d ∈ DK, UC6S846.rhoL K ⟨b, hbK⟩ d = d ^ (e * e) := by
  subst hLg
  obtain ⟨φ, hφ⟩ := uc22r3e5c_exists_bar2_conj_link g L
  have hα3 : (UC6S846.rhoL L ⟨b, hbL⟩) ^ 3 = 1 := uc22r3e5c_rhoL_pow_three hbL hb3
  have hαinv : (UC6S846.rhoL L ⟨b, hbL⟩)⁻¹ = (UC6S846.rhoL L ⟨b, hbL⟩) ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hα3])
  have hcomp : (UC6S846.rhoL (L.map (MulAut.conj g).toMonoidHom) ⟨b, hbK⟩).toMonoidHom.comp
      φ.toMonoidHom =
      φ.toMonoidHom.comp ((UC6S846.rhoL L ⟨b, hbL⟩)⁻¹).toMonoidHom :=
    MonoidHom.ext fun z => uc22r3e5c_rhoL_conj_swap hgb hbL hbK φ hφ z
  have hULinv := uc22r3e5c_rhoL_inv_map_eq hbL hαinv hUL
  have hDLinv := uc22r3e5c_rhoL_inv_map_eq hbL hαinv hDLα
  obtain ⟨U', hU'⟩ := uc22r3e5c_sylowMap φ UL
  have hU'coe : (U' : Subgroup (Bar2 (L.map (MulAut.conj g).toMonoidHom))) =
      (UL : Subgroup (Bar2 L)).map φ.toMonoidHom := hU'
  have hC' : DL.map φ.toMonoidHom ≤
      normalizer (U' : Set (Bar2 (L.map (MulAut.conj g).toMonoidHom))) :=
    (Subgroup.map_mono hDL).trans_eq (by
      rw [Subgroup.map_equiv_normalizer_eq (UL : Subgroup (Bar2 L)) φ, ← hU'coe]
      rfl)
  have hcase := uc22r3e5c_map_swap hbL hbK φ hcomp hDLinv
  have hUcase : (U' : Subgroup (Bar2 (L.map (MulAut.conj g).toMonoidHom))).map
      (UC6S846.rhoL (L.map (MulAut.conj g).toMonoidHom) ⟨b, hbK⟩).toMonoidHom = U' := by
    rw [hU'coe]
    exact uc22r3e5c_map_swap hbL hbK φ hcomp hULinv
  have hcard' : Nat.card (DL.map φ.toMonoidHom) = 2 ^ n - 1 := by
    rw [Subgroup.card_map_of_injective φ.injective, hDLc]
  exact uc22r3e5c_torusExp_eq (e := e * e) hSzK
    (UC6S846.rhoL (L.map (MulAut.conj g).toMonoidHom) ⟨b, hbK⟩) U' UK
    (DL.map φ.toMonoidHom) DK hC' hDK hcard' hDKc hUcase hcase hUK hDKα
    (uc22r3e5c_torusExp_swap_he hbL hbK hgb hαinv hDLα he φ hφ)

end CFSG.LocalAnalysis.UniquenessCase.UC22
