module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Map
import CFSG.GroupTheory.Frattini.PSubgroupLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup

private theorem exists_pSubgroup_lift {L : Type*} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hZp : Nat.Coprime (Nat.card (center L)) p) (σ : MulAut L) (σ' : MulAut (L ⧸ center L))
    (hσ : ∀ l : L, σ' (l : L ⧸ center L) = ((σ l : L) : L ⧸ center L))
    {y : L ⧸ center L} (hy : orderOf y = p) (hσy : σ' y = y⁻¹)
    {R : Subgroup (L ⧸ center L)} (hR : IsPGroup p R) (hyR : y ∈ R) :
    ∃ (A : Subgroup L) (e : ↥A ≃* ↥R) (x : ↥A), IsPGroup p A ∧
      A.map (QuotientGroup.mk' (center L)) = R ∧ A ⊓ center L = ⊥ ∧
      CFSG.ABGLocalTools.IsSylowOf p A (R.comap (QuotientGroup.mk' (center L))) ∧
      (∀ a : ↥A, ((e a : ↥R) : L ⧸ center L) = (QuotientGroup.mk' (center L)) (a : L)) ∧
      (∀ a b : ↥A, (QuotientGroup.mk' (center L)) (a : L) =
        (QuotientGroup.mk' (center L)) (b : L) → a = b) ∧
      e x = ⟨y, hyR⟩ ∧ orderOf x = p ∧ σ (x : L) = (x : L)⁻¹ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hker : (QuotientGroup.mk' (center L)).ker = center L := QuotientGroup.ker_mk' (center L)
  have hnd : ¬ p ∣ Nat.card (center L) := (Nat.Prime.coprime_iff_not_dvd hp).mp hZp.symm
  obtain ⟨A, hAp, hAle, hAmap, hAdisj⟩ :=
    CFSG.GroupTheory.exists_pSubgroup_map_eq_of_coprime_ker (QuotientGroup.mk' (center L))
      (QuotientGroup.mk'_surjective (center L)) (by rw [hker]; exact hnd) hR
  have hdisj : A ⊓ center L = ⊥ := by rw [← hker]; exact hAdisj
  have hinj : ∀ a b : ↥A, (QuotientGroup.mk' (center L)) (a : L) =
      (QuotientGroup.mk' (center L)) (b : L) → a = b := by
    intro a b hab
    have h1 : (QuotientGroup.mk' (center L)) ((a : L) * (b : L)⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : (a : L) * (b : L)⁻¹ ∈ A ⊓ center L :=
      ⟨A.mul_mem a.2 (A.inv_mem b.2), by rw [← hker]; exact MonoidHom.mem_ker.mpr h1⟩
    rw [hdisj, Subgroup.mem_bot] at h2
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have hfmem : ∀ a : ↥A, (QuotientGroup.mk' (center L)) (a : L) ∈ R := by
    intro a
    rw [← hAmap]
    exact Subgroup.mem_map_of_mem _ a.2
  let f : ↥A →* ↥R := ((QuotientGroup.mk' (center L)).comp A.subtype).codRestrict R hfmem
  have hfval : ∀ a : ↥A, ((f a : ↥R) : L ⧸ center L) = (QuotientGroup.mk' (center L)) (a : L) :=
    fun _ => rfl
  have hfinj : Function.Injective f := by
    intro a b hab
    exact hinj a b (by rw [← hfval a, ← hfval b, hab])
  have hfsurj : Function.Surjective f := by
    intro r
    have hr : (r : L ⧸ center L) ∈ A.map (QuotientGroup.mk' (center L)) := by
      rw [hAmap]; exact r.2
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hr
    exact ⟨⟨a, ha⟩, Subtype.ext hae⟩
  let e : ↥A ≃* ↥R := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have heval : ∀ a : ↥A, ((e a : ↥R) : L ⧸ center L) = (QuotientGroup.mk' (center L)) (a : L) :=
    fun a => hfval a
  obtain ⟨x, hxe⟩ := e.surjective ⟨y, hyR⟩
  have hxval : (QuotientGroup.mk' (center L)) (x : L) = y := by
    have h := heval x
    rw [hxe] at h
    simpa using h.symm
  have hxp : (x : L) ^ p = 1 := by
    have h : (QuotientGroup.mk' (center L)) ((x : L) ^ p) = 1 := by
      rw [map_pow, hxval, ← hy, pow_orderOf_eq_one]
    have hmem : (x : L) ^ p ∈ A ⊓ center L :=
      ⟨A.pow_mem x.2 p, by rw [← hker]; exact MonoidHom.mem_ker.mpr h⟩
    rwa [hdisj, Subgroup.mem_bot] at hmem
  have hσq : ∀ l : L, (QuotientGroup.mk' (center L)) (σ l) =
      σ' ((QuotientGroup.mk' (center L)) l) := by
    intro l
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact (hσ l).symm
  have hcardR : Nat.card ↥(R.comap (QuotientGroup.mk' (center L))) =
      Nat.card (center L) * Nat.card ↥R := by
    rw [CFSG.GroupTheory.card_comap_eq_card_ker_mul_card _ (QuotientGroup.mk'_surjective _) R,
      hker]
  have hidx : A.relIndex (R.comap (QuotientGroup.mk' (center L))) = Nat.card (center L) := by
    have h1 := Subgroup.relIndex_mul_card A (R.comap (QuotientGroup.mk' (center L)))
    rw [inf_eq_left.mpr hAle, hcardR, Nat.card_congr e.toEquiv] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf p A (R.comap (QuotientGroup.mk' (center L))) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hAle, hAp, by rw [hidx]; exact hnd⟩
  refine ⟨A, e, x, hAp, hAmap, hdisj, hAsyl, heval, hinj, hxe, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe x]
    have hdvd : orderOf (x : L) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hxp
    have hne : orderOf (x : L) ≠ 1 := by
      intro h1
      rw [orderOf_eq_one_iff] at h1
      have h2 : orderOf y = 1 := by
        have hy1 : y = 1 := by
          rw [← hxval, h1]
          exact map_one _
        rw [hy1, orderOf_one]
      rw [hy] at h2
      exact hp.ne_one h2
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd h1 hne
    · exact h1
  ·
    have hσx : (QuotientGroup.mk' (center L)) (σ (x : L)) =
        ((QuotientGroup.mk' (center L)) (x : L))⁻¹ := by
      rw [hσq (x : L), hxval, hσy]
    have hmem : σ (x : L) * (x : L) ∈ center L := by
      rw [← hker, MonoidHom.mem_ker, map_mul, hσx, inv_mul_cancel]
    have hσp : (σ (x : L)) ^ p = 1 := by
      rw [← map_pow, hxp, map_one]
    have hcz : Commute (σ (x : L) * (x : L)) (x : L) :=
      ((Subgroup.mem_center_iff.mp hmem) (x : L)).symm
    have hcx : Commute (σ (x : L)) (x : L) := by
      rw [show σ (x : L) = (σ (x : L) * (x : L)) * (x : L)⁻¹ from by group]
      exact hcz.mul_left (Commute.inv_left (Commute.refl (x : L)))
    have hzp : (σ (x : L) * (x : L)) ^ p = 1 := by
      rw [hcx.mul_pow p, hσp, hxp, mul_one]
    have hdz : orderOf (σ (x : L) * (x : L)) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hzp
    have hz1 : σ (x : L) * (x : L) = 1 := by
      have hcard := Subgroup.orderOf_dvd_natCard (center L) hmem
      rcases (Nat.dvd_prime hp).mp hdz with h1 | h1
      · rwa [orderOf_eq_one_iff] at h1
      · exact absurd (h1 ▸ hcard) hnd
    have heq : σ (x : L) = (σ (x : L) * (x : L)) * (x : L)⁻¹ := by group
    rw [heq, hz1, one_mul]

private theorem map_conj_le_of_le_normalizer {G : Type*} [Group G] {U H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (U : Set G)) (hH : H ≤ U) :
    H.map (MulAut.conj g).toMonoidHom ≤ U := by
  rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hg]
  exact Subgroup.map_mono hH

private theorem map_conj_eq_of_le_isMulCommutative {G : Type*} [Group G] {U H : Subgroup G}
    (hH : H ≤ U) (hcomm : IsMulCommutative U) {u : G} (hu : u ∈ U) :
    H.map (MulAut.conj u).toMonoidHom = H := by
  have hc : ∀ h ∈ H, u * h * u⁻¹ = h := by
    intro h hh
    have h1 : u * h = h * u :=
      congrArg Subtype.val (hcomm.is_comm.comm ⟨u, hu⟩ ⟨h, hH hh⟩)
    rw [h1]; group
  refine le_antisymm ?_ ?_
  · intro a ha
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hc h hh]
    exact hh
  · intro h hh
    refine Subgroup.mem_map.mpr ⟨h, hh, ?_⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hc h hh

private theorem map_conj_mul_eq_of_le {G : Type*} [Group G] {U H : Subgroup G} (_hH : H ≤ U)
    (hcomm : IsMulCommutative U) {a b : G} (ha : a ∈ U)
    (hb : H.map (MulAut.conj b).toMonoidHom ≤ U) :
    H.map (MulAut.conj (a * b)).toMonoidHom = H.map (MulAut.conj b).toMonoidHom := by
  rw [map_mul,
    show (MulAut.conj a * MulAut.conj b).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom from rfl,
    ← Subgroup.map_map]
  exact map_conj_eq_of_le_isMulCommutative hb hcomm ha

private theorem map_map_conj {G H : Type*} [Group G] [Group H] (π : G →* H) (E : Subgroup G)
    (g : G) : (E.map (MulAut.conj g).toMonoidHom).map π =
      (E.map π).map (MulAut.conj (π g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

private theorem exists_lift_special {L : Type*} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hZp : Nat.Coprime (Nat.card (center L)) p) (σ : MulAut L) (σ' : MulAut (L ⧸ center L))
    (hσ : ∀ l : L, σ' (l : L ⧸ center L) = ((σ l : L) : L ⧸ center L))
    {y : L ⧸ center L} (hy : orderOf y = p) (hσy : σ' y = y⁻¹)
    (hgood : IsSpecialGood p y) :
    ∃ x : L, orderOf x = p ∧ σ x = x⁻¹ ∧ IsSpecialGood p x := by
  obtain ⟨H, e₀, N, hyH, hH, heN, h3⟩ := hgood
  obtain ⟨A, e, x, -, -, -, -, -, -, hxe, hxord, hσx⟩ :=
    exists_pSubgroup_lift hp hZp σ σ' hσ hy hσy (IsPGroup.of_card hH.2.1) hyH
  exact ⟨(x : L), by rw [Subgroup.orderOf_coe x]; exact hxord, hσx,
    A, e₀, N, x.2, IsSpecialType.of_mulEquiv e.symm hH, heN, h3⟩

private theorem exists_lift_orbit {L : Type*} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hZp : Nat.Coprime (Nat.card (center L)) p) (σ : MulAut L) (σ' : MulAut (L ⧸ center L))
    (hσ : ∀ l : L, σ' (l : L ⧸ center L) = ((σ l : L) : L ⧸ center L))
    {y : L ⧸ center L} (hy : orderOf y = p) (hσy : σ' y = y⁻¹)
    {U : Subgroup (L ⧸ center L)} {k : ℕ} (hyU : y ∈ U) (hU : IsElemAbelian p U)
    (hk : 16 ≤ k * dParam p)
    (hcount : ∀ D₀ : Subgroup (L ⧸ center L), D₀ ≤ U → D₀.relIndex U = p →
      k ≤ {D : Subgroup (L ⧸ center L) | y ∉ D ∧
        ∃ g ∈ normalizer (U : Set (L ⧸ center L)),
          D = D₀.map (MulAut.conj g).toMonoidHom}.ncard) :
    ∃ x : L, orderOf x = p ∧ σ x = x⁻¹ ∧ IsOrbitGood p x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Subgroup L) := Finite.of_injective _ SetLike.coe_injective
  have : Finite (Subgroup (L ⧸ center L)) := Finite.of_injective _ SetLike.coe_injective
  have hUp : IsPGroup p U := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hU.2 (g : L ⧸ center L) g.2)⟩
  obtain ⟨A, e, x, hAp, hAmap, hdisj, hAsyl, heval, hinj, hxe, hxord, hσx⟩ :=
    exists_pSubgroup_lift hp hZp σ σ' hσ hy hσy hUp hyU
  have hAle : A ≤ U.comap (QuotientGroup.mk' (center L)) := hAsyl.le
  have hxval : (QuotientGroup.mk' (center L)) (x : L) = y := by
    rw [← heval x, hxe]
  refine ⟨(x : L), by rw [Subgroup.orderOf_coe x]; exact hxord, hσx, A, k, x.2, ?_, hk, ?_⟩
  · refine ⟨⟨⟨fun a b => e.injective ?_⟩⟩, fun a ha => ?_⟩
    · rw [map_mul, map_mul]; exact hU.1.is_comm.comm _ _
    · have h : (⟨a, ha⟩ : ↥A) ^ p = 1 := by
        refine e.injective ?_
        rw [map_pow, map_one]
        exact Subtype.ext (hU.2 (e ⟨a, ha⟩ : L ⧸ center L) (e ⟨a, ha⟩).2)
      simpa using congrArg Subtype.val h
  · intro E₀ hE₀A hE₀idx
    have hle : E₀.map (QuotientGroup.mk' (center L)) ≤ U := by
      rw [← hAmap]; exact Subgroup.map_mono hE₀A
    have hcardE : Nat.card ↥(E₀.map (QuotientGroup.mk' (center L))) = Nat.card ↥E₀ := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun a : ↥E₀ => (⟨(QuotientGroup.mk' (center L)) (a : L),
          Subgroup.mem_map_of_mem _ a.2⟩ : ↥(E₀.map (QuotientGroup.mk' (center L)))))
        ⟨?_, ?_⟩).symm
      · intro a b hab
        have h : (QuotientGroup.mk' (center L)) (a : L) =
            (QuotientGroup.mk' (center L)) (b : L) := congrArg Subtype.val hab
        have h2 : (⟨a.1, hE₀A a.2⟩ : ↥A) = ⟨b.1, hE₀A b.2⟩ := hinj _ _ h
        exact Subtype.ext (congrArg (fun y : ↥A => (y : L)) h2)
      · intro d
        obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp d.2
        exact ⟨⟨a, ha⟩, Subtype.ext hae⟩
    have hidx : (E₀.map (QuotientGroup.mk' (center L))).relIndex U = p := by
      have h1 := Subgroup.relIndex_mul_card E₀ A
      rw [inf_eq_left.mpr hE₀A, hE₀idx] at h1
      have h2 := Subgroup.relIndex_mul_card (E₀.map (QuotientGroup.mk' (center L))) U
      rw [inf_eq_left.mpr hle, hcardE, ← Nat.card_congr e.toEquiv] at h2
      rw [← h1] at h2
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
    have hcount₀ := hcount (E₀.map (QuotientGroup.mk' (center L))) hle hidx
    have hmapinf : ∀ D : Subgroup (L ⧸ center L), D ≤ U →
        (A ⊓ D.comap (QuotientGroup.mk' (center L))).map (QuotientGroup.mk' (center L)) = D := by
      intro D hDU
      refine le_antisymm ?_ ?_
      · rintro d ⟨a, ha, rfl⟩
        exact ha.2
      · intro d hd
        have hdU : d ∈ U := hDU hd
        rw [← hAmap] at hdU
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hdU
        exact Subgroup.mem_map_of_mem _ ⟨ha, Subgroup.mem_comap.mpr hd⟩
    refine hcount₀.trans (Set.ncard_le_ncard_of_injOn
      (fun D : Subgroup (L ⧸ center L) => A ⊓ D.comap (QuotientGroup.mk' (center L)))
      ?_ ?_ ?_)
    · rintro D ⟨hyD, gb, hgbN, hD⟩
      have hDU : D ≤ U := by
        rw [hD]; exact map_conj_le_of_le_normalizer hgbN hle
      constructor
      · intro hx
        exact hyD (by rw [← hxval]; exact Subgroup.mem_comap.mp hx.2)
      · obtain ⟨g, hπg⟩ := QuotientGroup.mk'_surjective (center L) gb
        have hgN : (QuotientGroup.mk' (center L)) g ∈ normalizer (U : Set (L ⧸ center L)) := by
          rw [hπg]; exact hgbN
        obtain ⟨n, hn, m, hm, hgm⟩ :=
          CFSG.GroupTheory.exists_mul_mem_comap_and_normalizer (QuotientGroup.mk' (center L))
            hAle hAsyl hgN
        have hπm : (QuotientGroup.mk' (center L)) m =
            ((QuotientGroup.mk' (center L)) n)⁻¹ * gb := by
          have h2 : (QuotientGroup.mk' (center L)) g = (QuotientGroup.mk' (center L)) n *
              (QuotientGroup.mk' (center L)) m := by rw [hgm, map_mul]
          rw [hπg] at h2
          rw [h2]; group
        have hEmA : E₀.map (MulAut.conj m).toMonoidHom ≤ A := by
          rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp hm]
          exact Subgroup.map_mono hE₀A
        have himg : (E₀.map (MulAut.conj m).toMonoidHom).map (QuotientGroup.mk' (center L)) =
            D := by
          rw [map_map_conj, hπm]
          refine (map_conj_mul_eq_of_le hle hU.1 ?_ ?_).trans hD.symm
          · exact U.inv_mem (Subgroup.mem_comap.mp hn)
          · exact map_conj_le_of_le_normalizer hgbN hle
        have key : ∀ E₁ E₂ : Subgroup L, E₁ ≤ A → E₂ ≤ A →
            E₁.map (QuotientGroup.mk' (center L)) = E₂.map (QuotientGroup.mk' (center L)) →
            E₁ = E₂ := by
          intro E₁ E₂ h₁ h₂ heq
          refine le_antisymm ?_ ?_
          · intro a ha
            have hmem : (QuotientGroup.mk' (center L)) a ∈ E₂.map (QuotientGroup.mk' (center L)) :=
              by rw [← heq]; exact Subgroup.mem_map_of_mem _ ha
            obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hmem
            have hab : b = a := congrArg Subtype.val (hinj ⟨b, h₂ hb⟩ ⟨a, h₁ ha⟩ hba)
            rw [← hab]; exact hb
          · intro a ha
            have hmem : (QuotientGroup.mk' (center L)) a ∈ E₁.map (QuotientGroup.mk' (center L)) :=
              by rw [heq]; exact Subgroup.mem_map_of_mem _ ha
            obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hmem
            have hab : b = a := congrArg Subtype.val (hinj ⟨b, h₁ hb⟩ ⟨a, h₂ ha⟩ hba)
            rw [← hab]; exact hb
        exact ⟨m, hm, key _ _ inf_le_left hEmA ((hmapinf D hDU).trans himg.symm)⟩
    · rintro D₁ ⟨hyD₁, gb₁, hgb₁N, hD₁⟩ D₂ ⟨hyD₂, gb₂, hgb₂N, hD₂⟩ heq
      have hD₁U : D₁ ≤ U := by rw [hD₁]; exact map_conj_le_of_le_normalizer hgb₁N hle
      have hD₂U : D₂ ≤ U := by rw [hD₂]; exact map_conj_le_of_le_normalizer hgb₂N hle
      change A ⊓ D₁.comap (QuotientGroup.mk' (center L)) =
        A ⊓ D₂.comap (QuotientGroup.mk' (center L)) at heq
      rw [← hmapinf D₁ hD₁U, ← hmapinf D₂ hD₂U, heq]
    · exact Set.toFinite _

theorem exists_lift_good {L : Type*} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hZp : Nat.Coprime (Nat.card (center L)) p) (σ : MulAut L) (σ' : MulAut (L ⧸ center L))
    (hσ : ∀ l : L, σ' (l : L ⧸ center L) = ((σ l : L) : L ⧸ center L))
    {y : L ⧸ center L} (hy : orderOf y = p) (hσy : σ' y = y⁻¹)
    (hgood : IsSpecialGood p y ∨ IsOrbitGood p y) :
    ∃ x : L, orderOf x = p ∧ σ x = x⁻¹ ∧ (IsSpecialGood p x ∨ IsOrbitGood p x) := by
  rcases hgood with ⟨H, e₀, N, hyH, hH, heN, h3⟩ | ⟨U, k, hyU, hU, hk, hcount⟩
  · obtain ⟨x, hx, hσx, hg⟩ :=
      exists_lift_special hp hZp σ σ' hσ hy hσy ⟨H, e₀, N, hyH, hH, heN, h3⟩
    exact ⟨x, hx, hσx, Or.inl hg⟩
  · obtain ⟨x, hx, hσx, hg⟩ :=
      exists_lift_orbit hp hZp σ σ' hσ hy hσy hyU hU hk hcount
    exact ⟨x, hx, hσx, Or.inr hg⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
