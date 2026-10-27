module

public import CFSG.Quasithin.Background.InvolutionQuadratic
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.GroupTheory.ConjTransport
public import CFSG.Quasithin.Background.D2Offenders
public import CFSG.Quasithin.Background.FixVLattice
public import Mathlib.GroupTheory.IsSubnormal

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

variable {V : Type*} [CommGroup V]

private theorem u_fixes_mul_inv {U₀ : Subgroup (MulAut V)} {u : MulAut V}
    (hU₀u : ∀ x ∈ U₀, x * u = u * x)
    (hU₀fix : ∀ x ∈ U₀, ∀ w ∈ commV (Subgroup.zpowers u), x w = w)
    {x : MulAut V} (hx : x ∈ U₀) (v : V) : u (x v * v⁻¹) = x v * v⁻¹ := by
  have hux : u (x v) = x (u v) :=
    congrArg (fun f : MulAut V => f v) (hU₀u x hx).symm
  have hmem : v⁻¹ * (u v) ∈ commV (Subgroup.zpowers u) := by
    have h : u v * v⁻¹ ∈ commV (Subgroup.zpowers u) :=
      Subgroup.subset_closure ⟨u, Subgroup.mem_zpowers u, v, rfl⟩
    rwa [mul_comm (u v) v⁻¹] at h
  have hxd : x (v⁻¹ * (u v)) = v⁻¹ * (u v) := hU₀fix x hx _ hmem
  have h1 : u (x v) = x v * v⁻¹ * u v := by
    rw [hux]
    have huv : u v = v * (v⁻¹ * (u v)) := by group
    rw [huv, map_mul, hxd]
    group
  calc u (x v * v⁻¹) = u (x v) * (u v)⁻¹ := by rw [map_mul, map_inv]
    _ = (x v * v⁻¹ * u v) * (u v)⁻¹ := by rw [h1]
    _ = x v * v⁻¹ := by group

private theorem eq_or_eq_of_relIndex_eq_prime {G : Type*} [Group G] {D E U : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hDE : D ≤ E) (hEU : E ≤ U) (hDU : D.relIndex U = p) :
    E = D ∨ E = U := by
  have hmul := Subgroup.relIndex_mul_relIndex D E U hDE hEU
  have hdvd : D.relIndex E ∣ p := ⟨E.relIndex U, (hmul.trans hDU).symm⟩
  rcases hp.eq_one_or_self_of_dvd (D.relIndex E) hdvd with h1 | h1
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hDE)
  · refine Or.inr (le_antisymm hEU ?_)
    have h2 : E.relIndex U = 1 := by
      have h3 : p * E.relIndex U = p := by rw [← h1, hmul, hDU, h1]
      have h4 : p * E.relIndex U = p * 1 := by rw [h3, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hp.pos h4
    exact Subgroup.relIndex_eq_one.mp h2

private theorem fixV_eq_fixV_of_hyperplane [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {U U₀ : Subgroup (MulAut V)} {u : MulAut V}
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hexp : ∀ x ∈ U, x ^ p = 1)
    (huU : ∀ x ∈ U, u * x * u⁻¹ ∈ U) (hU₀ : U₀ ≤ U) (hU₀u : ∀ x ∈ U₀, x * u = u * x)
    (hU₀fix : ∀ x ∈ U₀, ∀ w ∈ commV (Subgroup.zpowers u), x w = w)
    {H : Subgroup (MulAut V)} (hHU : H ≤ U) (hHp : H.relIndex U = p)
    (hU₀H : ¬ U₀ ≤ H) (huH : H.map (MulAut.conj u).toMonoidHom ≠ H) :
    fixV H = fixV U := by
  classical
  set W : Subgroup V := fixV H with hW
  have hHuU : H.map (MulAut.conj u).toMonoidHom ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact huU x (hHU hx)
  have hmax : H ⊔ H.map (MulAut.conj u).toMonoidHom = U := by
    rcases eq_or_eq_of_relIndex_eq_prime hp le_sup_left (sup_le hHU hHuU) hHp with h | h
    · exfalso
      have hle : H.map (MulAut.conj u).toMonoidHom ≤ H := le_trans le_sup_right h.le
      have hcard : Nat.card (H.map (MulAut.conj u).toMonoidHom) = Nat.card H :=
        Subgroup.card_map_of_injective (MulAut.conj u).injective
      exact huH (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm))
    · exact h
  have hmax₀ : H ⊔ U₀ = U := by
    rcases eq_or_eq_of_relIndex_eq_prime hp le_sup_left (sup_le hHU hU₀) hHp with h | h
    · exfalso
      exact hU₀H (le_trans le_sup_right h.le)
    · exact h
  have key : ∀ x ∈ U₀, ∀ w ∈ W, x w = w := by
    intro x hxU₀ w hw
    have hxU : x ∈ U := hU₀ hxU₀
    set y : V := x w * w⁻¹ with hy
    have hyH : y ∈ fixV H := by
      rw [mem_fixV]
      intro h hh
      have hcomm' : h * x = x * h := (hcomm x hxU h (hHU hh)).symm
      have hw' : h w = w := (mem_fixV.mp hw) h hh
      calc h y = h (x w) * (h w)⁻¹ := by rw [hy, map_mul, map_inv]
        _ = x (h w) * (h w)⁻¹ := by
          rw [show h (x w) = x (h w) from congrArg (fun f : MulAut V => f w) hcomm']
        _ = x w * w⁻¹ := by rw [hw']
        _ = y := by rw [hy]
    have huy : u y = y := by
      simpa [hy] using u_fixes_mul_inv hU₀u hU₀fix hxU₀ w
    have hyHu : y ∈ fixV (H.map (MulAut.conj u).toMonoidHom) := by
      rw [mem_fixV]
      rintro _ ⟨h, hh, rfl⟩
      have huiy : u⁻¹ y = y := by
        have h1 : u (u⁻¹ y) = u y := by rw [huy, MulAut.apply_inv_self]
        exact u.injective h1
      calc (u * h * u⁻¹) y = u (h (u⁻¹ y)) := rfl
        _ = u (h y) := by rw [huiy]
        _ = u y := by rw [mem_fixV.mp hyH h hh]
        _ = y := huy
    have hyU : y ∈ fixV U := by
      have hsup : y ∈ fixV (H ⊔ H.map (MulAut.conj u).toMonoidHom) :=
        FixVLat.mem_fixV_sup hyH hyHu
      rwa [hmax] at hsup
    have hxy : x y = y := mem_fixV.mp hyU x hxU
    have hxw : x w = y * w := by rw [hy, mul_assoc, inv_mul_cancel, mul_one]
    have hpow : ∀ k : ℕ, (x ^ k) w = (y ^ k) * w := by
      intro k
      induction k with
      | zero => rw [pow_zero, MulAut.one_apply, pow_zero, one_mul]
      | succ k ih =>
        calc (x ^ (k + 1)) w = x ((x ^ k) w) := by rw [pow_succ']; rfl
          _ = x (y ^ k * w) := by rw [ih]
          _ = x (y ^ k) * x w := by rw [map_mul]
          _ = (x y) ^ k * x w := by rw [map_pow]
          _ = y ^ k * (y * w) := by rw [hxy, hxw]
          _ = y ^ (k + 1) * w := by rw [pow_succ]; group
    have hyp : y ^ p * w = w := by
      rw [← hpow p, hexp x hxU]
      simp
    have hyp1 : y ^ p = 1 := by
      have h1 : y ^ p * w = 1 * w := by rw [hyp, one_mul]
      exact mul_right_cancel_iff.mp h1
    have hodd : Odd p := hp.odd_of_ne_two hp2
    have hy1 : y = 1 := by
      obtain ⟨m, hm⟩ := hodd
      have h2 : y ^ 2 = 1 := by simpa [pow_two] using hV y
      have hyp' : y ^ p = y := by
        rw [hm, pow_add, pow_mul, h2, one_pow, one_mul, pow_one]
      rw [← hyp', hyp1]
    rw [hxw, hy1, one_mul]
  have hHcent : H ≤ centSub W := by
    intro h hh
    rw [mem_centSub]
    intro w hw
    exact (mem_fixV.mp (hW ▸ hw)) h hh
  have hUcent : U ≤ centSub W := by
    rw [← hmax₀]
    exact sup_le hHcent fun x hx => mem_centSub.mpr fun w hw => key x hx w hw
  refine le_antisymm ?_ (fixV_anti hHU)
  intro w hw
  rw [mem_fixV]
  intro x hx
  exact mem_centSub.mp (hUcent hx) w hw

private theorem fixV_eq_fixV_of_hyp [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {U U₀ : Subgroup (MulAut V)} {u : MulAut V}
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hexp : ∀ x ∈ U, x ^ p = 1)
    (huU : ∀ x ∈ U, u * x * u⁻¹ ∈ U) (hU₀ : U₀ ≤ U) (hU₀u : ∀ x ∈ U₀, x * u = u * x)
    (hU₀fix : ∀ x ∈ U₀, ∀ w ∈ commV (Subgroup.zpowers u), x w = w)
    (hhyp : ∀ H : Subgroup (MulAut V), H ≤ U → H.relIndex U = p →
      ∃ s : MulAut V, (∀ x ∈ U, s * x * s⁻¹ ∈ U) ∧
        ¬ U₀ ≤ H.map (MulAut.conj s).toMonoidHom ∧
        (H.map (MulAut.conj s).toMonoidHom).map (MulAut.conj u).toMonoidHom ≠
          H.map (MulAut.conj s).toMonoidHom)
    {H : Subgroup (MulAut V)} (hHU : H ≤ U) (hHp : H.relIndex U = p) :
    fixV H = fixV U := by
  classical
  obtain ⟨s, hsU, hsU₀, hsu⟩ := hhyp H hHU hHp
  have hUs : U.map (MulAut.conj s).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (CFSG.GroupTheory.mem_normalizer_of_conj_mem hsU)
  have hHs : H.map (MulAut.conj s).toMonoidHom ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsU x (hHU hx)
  have hHsp : (H.map (MulAut.conj s).toMonoidHom).relIndex U = p := by
    have h1 := Subgroup.relIndex_map_map_of_injective
      (f := (MulAut.conj s).toMonoidHom) H U (MulAut.conj s).injective
    rwa [hUs, hHp] at h1
  have hfixHs : fixV (H.map (MulAut.conj s).toMonoidHom) = fixV U :=
    fixV_eq_fixV_of_hyperplane hV hp hp2 hcomm hexp huU hU₀ hU₀u hU₀fix hHs hHsp hsU₀ hsu
  have hfin : (fixV H).map s.toMonoidHom = fixV U := by
    rw [← fixV_map_conj_eq H s]
    exact hfixHs
  have hfixUs : (fixV U).map s.toMonoidHom = fixV U := by
    rw [← fixV_map_conj_eq U s, hUs]
  have hmap_inv : ∀ X : Subgroup V, (X.map s.toMonoidHom).map (s⁻¹).toMonoidHom = X := by
    intro X
    rw [Subgroup.map_map]
    have h : (s⁻¹).toMonoidHom.comp s.toMonoidHom = MonoidHom.id V := by
      ext v
      simp
    rw [h, Subgroup.map_id]
  have hfixUsinv : (fixV U).map (s⁻¹).toMonoidHom = fixV U := by
    calc (fixV U).map (s⁻¹).toMonoidHom
        = ((fixV U).map s.toMonoidHom).map (s⁻¹).toMonoidHom := by rw [hfixUs]
      _ = fixV U := hmap_inv (fixV U)
  calc fixV H = ((fixV H).map s.toMonoidHom).map (s⁻¹).toMonoidHom :=
        (hmap_inv (fixV H)).symm
    _ = (fixV U).map (s⁻¹).toMonoidHom := by rw [hfin]
    _ = fixV U := hfixUsinv

theorem false_of_stab_commV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)}
    (hL : IsSimpleGroup ↥L) (hZ : center ↥L = ⊥) (hfix : fixV L = ⊥) {t t₀ : MulAut V}
    (ht : t * t = 1) (ht₀ : t₀ ∈ L) (ht₀1 : t₀ ≠ 1)
    (htt₀ : t₀⁻¹ * t ∈ centralizer (L : Set (MulAut V)))
    (hstab : ∀ l ∈ L, ∀ w ∈ commV (zpowers t), l w ∈ commV (zpowers t)) : False := by
  classical
  set W : Subgroup V := commV (Subgroup.zpowers t) with hW
  set c : MulAut V := t₀⁻¹ * t with hc
  have hcL : ∀ l ∈ L, l * c = c * l := fun l hl =>
    (Subgroup.mem_centralizer_iff.mp htt₀) l hl
  have hct₀ : t₀ * c = c * t₀ := hcL t₀ ht₀
  have ht_eq : t = t₀ * c := by rw [hc]; group
  have hct : c * t = t * c := by
    calc c * t = c * (t₀ * c) := by rw [ht_eq]
      _ = (c * t₀) * c := by rw [← mul_assoc]
      _ = (t₀ * c) * c := by rw [← hct₀]
      _ = t * c := by rw [← ht_eq]
  have hct' : c * t * c⁻¹ = t := by
    rw [hct, mul_assoc, mul_inv_cancel, mul_one]
  have hWc : W.map c.toMonoidHom = W := by
    rw [hW, ← commV_zpowers_conj_eq t c, hct']
  have hWc_mem : ∀ w ∈ W, c w ∈ W := by
    intro w hw
    have h : c w ∈ W.map c.toMonoidHom := Subgroup.mem_map_of_mem _ hw
    rwa [hWc] at h
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact ht
  have hWt : ∀ w ∈ W, t w = w := by
    intro w hw
    exact (mem_fixV.mp ((commV_zpowers_le_fixV_of_involution hV ht2) hw)) t
      (Subgroup.mem_zpowers t)
  have hKn : ((L ⊓ centSub W).subgroupOf L).Normal := by
    refine Subgroup.Normal.mk (fun n hn g => ?_)
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hcoe : (↑(g * n * g⁻¹) : MulAut V) =
        (g : MulAut V) * (n : MulAut V) * (g : MulAut V)⁻¹ := rfl
    rw [hcoe]
    refine ⟨L.mul_mem (L.mul_mem g.2 hn.1) (L.inv_mem g.2), ?_⟩
    refine mem_centSub.mpr fun w hw => ?_
    have hgw : (g : MulAut V)⁻¹ w ∈ W := hstab (g : MulAut V)⁻¹ (L.inv_mem g.2) w hw
    have hnw : (n : MulAut V) ((g : MulAut V)⁻¹ w) = (g : MulAut V)⁻¹ w :=
      mem_centSub.mp hn.2 _ hgw
    calc ((g : MulAut V) * (n : MulAut V) * (g : MulAut V)⁻¹) w
        = (g : MulAut V) ((n : MulAut V) ((g : MulAut V)⁻¹ w)) := rfl
      _ = (g : MulAut V) ((g : MulAut V)⁻¹ w) := by rw [hnw]
      _ = w := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hL hKn.isSubnormal with hbot | htop
  ·
    have ht₀W : ∀ w ∈ W, t₀ w = c⁻¹ w := by
      intro w hw
      have h1 : t₀ (c w) = w := by
        rw [← MulAut.mul_apply, ← ht_eq]
        exact hWt w hw
      have h2 : c (t₀ w) = w := by
        calc c (t₀ w) = (c * t₀) w := rfl
          _ = (t₀ * c) w := by rw [← hct₀]
          _ = t₀ (c w) := rfl
          _ = w := h1
      calc t₀ w = c⁻¹ (c (t₀ w)) := by
            rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
        _ = c⁻¹ w := by rw [h2]
    have ht₀invW : ∀ w ∈ W, t₀⁻¹ w = c w := by
      intro w hw
      have h1 : t₀ (c w) = w := by
        rw [← MulAut.mul_apply, ← ht_eq]
        exact hWt w hw
      calc t₀⁻¹ w = t₀⁻¹ (t₀ (c w)) := by rw [h1]
        _ = c w := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    have hkey : ∀ l ∈ L, l * t₀ * l⁻¹ * t₀⁻¹ ∈ centSub W := by
      intro l hl
      rw [mem_centSub]
      intro w hw
      have hlw : l⁻¹ w ∈ W := hstab l⁻¹ (L.inv_mem hl) w hw
      have hcwl : c (l⁻¹ w) = l⁻¹ (c w) := by
        have h : l⁻¹ * c = c * l⁻¹ := hcL l⁻¹ (L.inv_mem hl)
        show (c * l⁻¹) w = (l⁻¹ * c) w
        rw [h]
      calc (l * t₀ * l⁻¹ * t₀⁻¹) w = l (t₀ (l⁻¹ (t₀⁻¹ w))) := rfl
        _ = l (t₀ (l⁻¹ (c w))) := by rw [ht₀invW w hw]
        _ = l (t₀ (c (l⁻¹ w))) := by rw [hcwl]
        _ = l (l⁻¹ w) := by
          have hc1 : c⁻¹ (c (l⁻¹ w)) = l⁻¹ w := by
            rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
          rw [ht₀W (c (l⁻¹ w)) (hWc_mem (l⁻¹ w) hlw), hc1]
        _ = w := by
          have hl1 : l (l⁻¹ w) = w := by
            rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
          rw [hl1]
    have hone : ∀ l ∈ L, l * t₀ * l⁻¹ * t₀⁻¹ = 1 := by
      intro l hl
      have hLKmem : l * t₀ * l⁻¹ * t₀⁻¹ ∈ L :=
        L.mul_mem (L.mul_mem (L.mul_mem hl ht₀) (L.inv_mem hl)) (L.inv_mem ht₀)
      have hmem : (⟨l * t₀ * l⁻¹ * t₀⁻¹, hLKmem⟩ : ↥L) ∈
          (L ⊓ centSub W).subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨hLKmem, hkey l hl⟩
      rw [hbot] at hmem
      have h1 : (⟨l * t₀ * l⁻¹ * t₀⁻¹, hLKmem⟩ : ↥L) = 1 := Subgroup.mem_bot.mp hmem
      simpa using congrArg Subtype.val h1
    have hcenter : (⟨t₀, ht₀⟩ : ↥L) ∈ Subgroup.center ↥L := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      apply Subtype.ext
      have h1 := hone (y : MulAut V) y.2
      show (y : MulAut V) * t₀ = t₀ * (y : MulAut V)
      calc (y : MulAut V) * t₀
          = ((y : MulAut V) * t₀ * (y : MulAut V)⁻¹ * t₀⁻¹) * (t₀ * (y : MulAut V)) := by
            group
        _ = t₀ * (y : MulAut V) := by rw [h1, one_mul]
    have htriv : (⟨t₀, ht₀⟩ : ↥L) = 1 := by
      rw [hZ] at hcenter
      exact Subgroup.mem_bot.mp hcenter
    exact ht₀1 (by simpa using congrArg Subtype.val htriv)
  ·
    have hLK : L ≤ L ⊓ centSub W := by
      intro l hl
      have hmem : (⟨l, hl⟩ : ↥L) ∈ (L ⊓ centSub W).subgroupOf L := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    have hWbot : W = ⊥ := by
      have hWL : W ≤ fixV L := by
        intro w hw
        rw [mem_fixV]
        intro l hl
        exact mem_centSub.mp (hLK hl).2 w hw
      exact le_bot_iff.mp (le_trans hWL (le_of_eq hfix))
    have ht1 : t = 1 := by
      ext v
      have hmem : t v * v⁻¹ ∈ W :=
        Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, v, rfl⟩
      rw [hWbot, Subgroup.mem_bot] at hmem
      rwa [mul_inv_eq_one] at hmem
    have ht₀eq : t₀ = c⁻¹ := by
      have h1 : t * c⁻¹ = t₀ := by rw [ht_eq]; group
      rw [← h1, ht1, one_mul]
    have hcenter : (⟨t₀, ht₀⟩ : ↥L) ∈ Subgroup.center ↥L := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      apply Subtype.ext
      show (y : MulAut V) * t₀ = t₀ * (y : MulAut V)
      rw [ht₀eq]
      exact (Commute.inv_right (show Commute (y : MulAut V) c from hcL y y.2)).eq
    have htriv : (⟨t₀, ht₀⟩ : ↥L) = 1 := by
      rw [hZ] at hcenter
      exact Subgroup.mem_bot.mp hcenter
    exact ht₀1 (by simpa using congrArg Subtype.val htriv)

theorem eq_bot_of_hyperplanes [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {U U₀ : Subgroup (MulAut V)} {u : MulAut V}
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hexp : ∀ x ∈ U, x ^ p = 1)
    (huU : ∀ x ∈ U, u * x * u⁻¹ ∈ U) (hU₀ : U₀ ≤ U) (hU₀u : ∀ x ∈ U₀, x * u = u * x)
    (hU₀fix : ∀ x ∈ U₀, ∀ w ∈ commV (zpowers u), x w = w)
    (hhyp : ∀ H : Subgroup (MulAut V), H ≤ U → H.relIndex U = p →
      ∃ s : MulAut V, (∀ x ∈ U, s * x * s⁻¹ ∈ U) ∧
        ¬ U₀ ≤ H.map (MulAut.conj s).toMonoidHom ∧
        (H.map (MulAut.conj s).toMonoidHom).map (MulAut.conj u).toMonoidHom ≠
          H.map (MulAut.conj s).toMonoidHom) :
    U = ⊥ := by
  classical
  by_cases hU : U = ⊥
  · exact hU
  · exfalso
    have hfact : Fact p.Prime := ⟨hp⟩
    have hnt : Nontrivial ↥U := (Subgroup.nontrivial_iff_ne_bot U).mpr hU
    have hel : CFSG.IsElementaryAbelian p ↥U :=
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
          Subtype.ext (by simpa using hexp x x.2) }
    let _ : MulDistribMulAction ↥U V := MulDistribMulAction.compHom V U.subtype
    have hpV : ¬ p ∣ Nat.card V := by
      rw [← Subgroup.card_top (G := V), card_eq_two_pow hV ⊤]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    have hgen : ⨆ (B : Subgroup ↥U) (_ : B.index = p), fixedPointSubgroup ↥B V = ⊤ :=
      CFSG.SolvableHall.abelian_hyperplane_generation (p := p) (A := ↥U) (H := V) hpV
    have htop : fixV U = ⊤ := by
      refine top_le_iff.mp ?_
      rw [← hgen]
      refine iSup₂_le fun B hB => ?_
      have hBU : B.map U.subtype ≤ U := Subgroup.map_subtype_le B
      have hBrel : (B.map U.subtype).relIndex U = p := by
        have h1 := Subgroup.relIndex_map_map_of_injective
          (f := U.subtype) B ⊤ U.subtype_injective
        rw [Subgroup.map_top, Subgroup.subtype_range, Subgroup.relIndex_top_right] at h1
        exact h1.trans hB
      have hBfix := fixV_eq_fixV_of_hyp hV hp hp2 hcomm hexp huU hU₀ hU₀u hU₀fix hhyp hBU hBrel
      refine le_trans ?_ (le_of_eq hBfix)
      intro v hv
      rw [mem_fixV]
      intro x hx
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
      exact hv ⟨b, hb⟩
    have hval : U = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      ext v
      have hv : v ∈ fixV U := by rw [htop]; exact Subgroup.mem_top v
      simpa using (mem_fixV.mp hv) x hx
    exact hU hval

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
