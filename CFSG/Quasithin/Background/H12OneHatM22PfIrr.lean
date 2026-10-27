module

public import CFSG.Quasithin.Background.SmithB45HM22Holds
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.B4ModelsIso

public section

namespace CFSG.Quasithin.H.Mathieu.H12Pf

open CFSG.Quasithin

section Nat

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)} {π : ↥Γ →* ↥H}

theorem exists_coord_of_realizesVia (hπ : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π) :
    ∃ E : W ≃* Multiplicative (ι → K), ∀ (γ : ↥Γ) (w : W),
      Multiplicative.toAdd (E (((π γ : ↥H) : MulAut W) w)) =
        ((γ : GL ι K) : Matrix ι ι K).mulVec (Multiplicative.toAdd (E w)) := by
  set D := FFModel.nat Γ with hD
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  let q : (↥D.sec ⧸ D.ker.subgroupOf D.sec) →* D.Amb :=
    QuotientGroup.lift _ D.sec.subtype (by
      intro m hm
      rw [Subgroup.mem_subgroupOf] at hm
      exact Subgroup.mem_bot.mp hm)
  have hq : ∀ m : ↥D.sec, q (QuotientGroup.mk m) = (m : D.Amb) := fun m => rfl
  let e0 : W →* D.Amb := q.comp (β.comp Subgroup.topEquiv.symm.toMonoidHom)
  have he0 : ∀ w, e0 w = q (β ⟨w, trivial⟩) := fun w => rfl
  have hinj : Function.Injective e0 := by
    rw [injective_iff_map_eq_one]
    intro w hw
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, trivial⟩)
    rw [he0, ← hm, hq] at hw
    have h1 : β ⟨w, trivial⟩ = 1 := by
      rw [← hm, show m = 1 from Subtype.ext hw]
      rfl
    exact Subgroup.mem_bot.mp ((hβk ⟨w, trivial⟩).mp h1)
  have hsurj : Function.Surjective e0 := by
    intro y
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨y, trivial⟩)
    refine ⟨u, ?_⟩
    rw [he0, show (⟨(u : W), trivial⟩ : ↥(⊤ : Subgroup W)) = u from rfl, hu]
    rfl
  refine ⟨MulEquiv.ofBijective e0 ⟨hinj, hsurj⟩, fun γ w => ?_⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, trivial⟩)
  have h1 : β ⟨((π γ : ↥H) : MulAut W) w, trivial⟩ =
      QuotientGroup.mk ⟨D.act γ (m : D.Amb), trivial⟩ :=
    hβe γ ⟨w, trivial⟩ m trivial trivial hm.symm
  show Multiplicative.toAdd (e0 _) =
    ((γ : GL ι K) : Matrix ι ι K).mulVec (Multiplicative.toAdd (e0 w))
  rw [he0, he0, h1, ← hm, hq, hq]
  rfl

theorem card_eq_of_realizesVia (hπ : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π) :
    Nat.card W = Nat.card K ^ Fintype.card ι := by
  obtain ⟨E, -⟩ := exists_coord_of_realizesVia hπ
  rw [Nat.card_congr E.toEquiv, Nat.card_congr (Multiplicative.toAdd : _ ≃ (ι → K)),
    Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]

end Nat

theorem isHat_of_mulEquiv {A B S : Type} [Group A] [Group B] [Group S] (e : A ≃* B)
    (h : IsHat A S) : IsHat B S := by
  obtain ⟨hq, hz, ⟨f⟩⟩ := h
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, ⟨?_⟩⟩
  · rw [← hz]
    exact Nat.card_congr (Subgroup.centerCongr e).toEquiv.symm
  · exact (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)).trans f

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}

theorem card_eq_of_mhat22Twelve (h : Mhat22Twelve L ⊤ ⊥) : Nat.card W = 4096 := by
  obtain ⟨K, _, _, Γ₀, hK, -, -, π, hπ⟩ := h
  rw [card_eq_of_realizesVia hπ, hK, Fintype.card_fin]
  norm_num

theorem isHat_of_mhat22Twelve (h : Mhat22Twelve L ⊤ ⊥) :
    IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
  obtain ⟨K, _, _, Γ₀, -, hhat, -, π, hπ⟩ := h
  have hinj := hπ.injective_of_faithful (FFModel.nat_faithful Γ₀)
  exact isHat_of_mulEquiv (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩) hhat

theorem mem_zpowers_of_center {X : Type*} [Group X] (h3 : Nat.card (Subgroup.center X) = 3)
    {z x : X} (hz : z ∈ Subgroup.center X) (hx : x ∈ Subgroup.center X) (hx1 : x ≠ 1) :
    z ∈ Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop := zpowers_eq_top_of_prime_card h3 (g := ⟨x, hx⟩)
    (fun h => hx1 (congrArg Subtype.val h))
  have hz' : (⟨z, hz⟩ : ↥(Subgroup.center X)) ∈
      Subgroup.zpowers (⟨x, hx⟩ : ↥(Subgroup.center X)) := htop ▸ Subgroup.mem_top _
  obtain ⟨k, hk⟩ := hz'
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem autSubEquivOfFaithful_apply_val {U : Subgroup W} (hLU : L ≤ stabSub U)
    (hfaith : L ⊓ centSub U = ⊥) (g : ↥L) (u : ↥U) :
    ((((autSubEquivOfFaithful hLU hfaith g : ↥(autSub L U)) : MulAut ↥U) u : ↥U) : W) =
      (g : MulAut W) u := by
  rw [autSubEquivOfFaithful_apply]
  rfl

theorem le_card_of_fpf
    [Finite W] (hV : ∀ w : W, w ^ 2 = 1)
    (hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22)) (hW : Nat.card W < 2 ^ 30)
    {z : ↥L} (hz : z ∈ Subgroup.center ↥L) :
    ∀ (n : ℕ) (U : Subgroup W), Nat.card U = n → U ≠ ⊥ →
      (∀ g : ↥L, ∀ u ∈ U, (g : MulAut W) u ∈ U) →
      (∀ u ∈ U, (z : MulAut W) u = u → u = 1) → 4096 ≤ Nat.card U := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hUn hU hinv hfix
  by_cases hmin : ∃ U' : Subgroup W, U' < U ∧ U' ≠ ⊥ ∧ ∀ g : ↥L, ∀ u ∈ U', (g : MulAut W) u ∈ U'
  · obtain ⟨U', hlt, hU'0, hinv'⟩ := hmin
    have hcard : Nat.card U' < n := hUn ▸ Subgroup.card_lt_of_lt hlt
    exact (ih _ hcard U' rfl hU'0 hinv' fun u hu => hfix u (hlt.le hu)).trans
      (Subgroup.card_le_of_le hlt.le)
  have hmin' : ∀ U' : Subgroup W, U' ≤ U → U' ≠ ⊥ →
      (∀ g : ↥L, ∀ u ∈ U', (g : MulAut W) u ∈ U') → U' = U := by
    intro U' hle h0 hinv'
    by_contra hne
    exact hmin ⟨U', lt_of_le_of_ne hle hne, h0, hinv'⟩
  have hLU : L ≤ stabSub U := by
    intro g hg u
    refine ⟨fun hu => ?_, fun hu => hinv ⟨g, hg⟩ u hu⟩
    have := hinv ⟨g⁻¹, L.inv_mem hg⟩ _ hu
    simpa using this
  obtain ⟨⟨u₀, hu₀⟩, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  have hu₀1' : u₀ ≠ 1 := fun h => hu₀1 (Subtype.ext h)
  have hzU : z ∉ (L ⊓ centSub U).subgroupOf L := fun h =>
    hu₀1' (hfix u₀ hu₀ ((Subgroup.mem_subgroupOf.mp h).2 u₀ hu₀))
  have hfaith : L ⊓ centSub U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hN : ((L ⊓ centSub U).subgroupOf L).Normal := by
      refine ⟨fun a ha g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      refine ⟨L.mul_mem (L.mul_mem g.2 ha.1) (L.inv_mem g.2), fun u hu => ?_⟩
      have hu' : (g : MulAut W)⁻¹ u ∈ U := (hLU (L.inv_mem g.2) u).2 hu
      change (g : MulAut W) ((a : MulAut W) ((g : MulAut W)⁻¹ u)) = u
      rw [ha.2 _ hu']
      simp
    have hq : CFSG.Open.IsQuasisimple ↥L := by
      have := hL.1.1
      exact ⟨Group.IsPerfect.commutator_eq_top, hL.1.2.1⟩
    have hxL : (⟨x, hx.1⟩ : ↥L) ∈ (L ⊓ centSub U).subgroupOf L :=
      Subgroup.mem_subgroupOf.mpr hx
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      ((L ⊓ centSub U).subgroupOf L) with hc | htop
    · exact hzU ((Subgroup.zpowers_le.mpr hxL)
        (mem_zpowers_of_center hL.2.1 hz (hc hxL) (fun h => hx1 (congrArg Subtype.val h))))
    · exact hzU (htop ▸ Subgroup.mem_top z)
  set e := autSubEquivOfFaithful hLU hfaith with he
  have hirr : XMod.IsIrrSec ↥(autSub L U) (⊥ : Subgroup ↥U) ⊤ := by
    refine ⟨bot_lt_iff_ne_bot.mpr fun h => hu₀1 ?_, fun J hJ _ _ => ?_⟩
    · have := Subgroup.mem_top (⟨u₀, hu₀⟩ : ↥U)
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    · have hJ'U : J.map U.subtype ≤ U := by
        rintro _ ⟨j, -, rfl⟩
        exact j.2
      have hJ'inv : ∀ g : ↥L, ∀ u ∈ J.map U.subtype, (g : MulAut W) u ∈ J.map U.subtype := by
        rintro g _ ⟨j, hj, rfl⟩
        refine ⟨(e g) • j, hJ (e g) j hj, ?_⟩
        exact autSubEquivOfFaithful_apply_val hLU hfaith g j
      by_cases hJ0 : J.map U.subtype = ⊥
      · left
        rw [eq_bot_iff]
        intro j hj
        have : (j : W) ∈ J.map U.subtype := ⟨j, hj, rfl⟩
        rw [hJ0] at this
        exact Subtype.ext (Subgroup.mem_bot.mp this)
      · right
        have hJ'eq := hmin' _ hJ'U hJ0 hJ'inv
        rw [eq_top_iff]
        intro j _
        have : (j : W) ∈ J.map U.subtype := by
          rw [hJ'eq]
          exact j.2
        obtain ⟨j', hj', hjj'⟩ := this
        have : j' = j := Subtype.ext hjj'
        exact this ▸ hj'
  have hhat : IsHat ↥(autSub L U) (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    isHat_of_mulEquiv e hL
  have hV' : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV v)
  have hcardU : Nat.card ↥U < 2 ^ 30 := lt_of_le_of_lt (Subgroup.card_le_card_group U) hW
  obtain ⟨π, hπ⟩ := hatM22SmallModules_holds ↥U hV' (autSub L U) hhat hirr hcardU
  have h4 := card_eq_of_realizesVia hπ
  rw [CFSG.CharacterTheory.SteinbergBY.FieldFour.natCard_eq, Fintype.card_fin] at h4
  rw [h4]
  norm_num

theorem fpf_of_mhat22Twelve
    [Finite W] (hV : ∀ w : W, w ^ 2 = 1)
    (h : Mhat22Twelve L ⊤ ⊥) {z : ↥L} (hz : z ∈ Subgroup.center ↥L) (hz1 : z ≠ 1) :
    ∀ w : W, (z : MulAut W) w = w → w = 1 := by
  have hW := card_eq_of_mhat22Twelve h
  have hL := isHat_of_mhat22Twelve h
  set zz : MulAut W := (z : MulAut W) with hzz
  have hz3 : ∀ w : W, zz (zz (zz w)) = w := by
    have h1 : (⟨z, hz⟩ : ↥(Subgroup.center ↥L)) ^ 3 = 1 := by
      rw [← hL.2.1]
      exact pow_card_eq_one'
    have h2 : zz ^ 3 = 1 := by
      have := congrArg (fun x : ↥(Subgroup.center ↥L) => ((x : ↥L) : MulAut W)) h1
      simpa [hzz] using this
    intro w
    have := congrArg (fun φ : MulAut W => φ w) h2
    simpa [pow_succ, MulAut.mul_apply] using this
  have hcomm : ∀ (g : ↥L) (w : W), zz ((g : MulAut W) w) = (g : MulAut W) (zz w) := by
    intro g w
    have := congrArg (fun x : ↥L => (x : MulAut W) w) (Subgroup.mem_center_iff.mp hz g)
    simpa [hzz, MulAut.mul_apply] using this.symm
  have hsq : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hV w
  let N : W →* W := MonoidHom.id W * zz.toMonoidHom * (zz * zz).toMonoidHom
  have hN : ∀ w, N w = w * zz w * zz (zz w) := fun w => rfl
  have hfixN : ∀ w ∈ N.ker, zz w = w → w = 1 := by
    intro w hw hzw
    rw [MonoidHom.mem_ker, hN, hzw, hzw, hsq, one_mul] at hw
    exact hw
  have hinvN : ∀ g : ↥L, ∀ w ∈ N.ker, (g : MulAut W) w ∈ N.ker := by
    intro g w hw
    rw [MonoidHom.mem_ker] at hw ⊢
    rw [hN, hcomm, hcomm, ← map_mul, ← map_mul, ← hN, hw, map_one]
  have hne : N.ker ≠ ⊥ := by
    have hzz1 : zz ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
    obtain ⟨w, hw⟩ : ∃ w, zz w ≠ w := by
      by_contra hall
      push Not at hall
      exact hzz1 (MulEquiv.ext hall)
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨w * zz w, ?_⟩, fun h1 => hw ?_⟩
    · rw [MonoidHom.mem_ker, hN, map_mul, map_mul, hz3]
      calc w * zz w * (zz w * zz (zz w)) * (zz (zz w) * w)
          = (w * w) * (zz w * zz w) * (zz (zz w) * zz (zz w)) := by ac_rfl
        _ = 1 := by simp only [hsq]
    · have h2 : w * zz w = 1 := congrArg Subtype.val h1
      calc zz w = w * (w * zz w) := by rw [← mul_assoc, hsq, one_mul]
        _ = w := by rw [h2, mul_one]
  have hcard := le_card_of_fpf hV hL (by rw [hW]; norm_num) hz _ N.ker rfl hne hinvN hfixN
  have htop : N.ker = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) (hW ▸ hcard))
  intro w hw
  have h1 : N w = 1 := by
    rw [← MonoidHom.mem_ker, htop]
    exact Subgroup.mem_top w
  rw [hN, hw, hw, hsq, one_mul] at h1
  exact h1

theorem isIrrSec_of_mhat22Twelve
    [Finite W] (hV : ∀ w : W, w ^ 2 = 1)
    (h : Mhat22Twelve L ⊤ ⊥) : XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤ := by
  have hW := card_eq_of_mhat22Twelve h
  have hL := isHat_of_mhat22Twelve h
  have : Nontrivial ↥(Subgroup.center ↥L) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hL.2.1]
    norm_num
  obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥L))
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hfix := fpf_of_mhat22Twelve hV h hz hz1'
  refine ⟨bot_lt_iff_ne_bot.mpr fun h0 => ?_, fun J hJ _ _ => ?_⟩
  · have : Nat.card (⊤ : Subgroup W) = 1 := by rw [h0, Subgroup.card_bot]
    rw [Subgroup.card_top, hW] at this
    norm_num at this
  · by_cases hJ0 : J = ⊥
    · exact Or.inl hJ0
    · right
      have hcard := le_card_of_fpf hV hL (by rw [hW]; norm_num) hz _ J rfl hJ0
        (fun g u hu => hJ g u hu) (fun u _ hu => hfix u hu)
      exact Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _)
        (hW ▸ hcard))

end CFSG.Quasithin.H.Mathieu.H12Pf
