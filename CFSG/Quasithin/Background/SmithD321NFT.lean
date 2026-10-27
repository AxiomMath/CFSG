module

public import CFSG.Quasithin.Background.F918P0
public import CFSG.Quasithin.Background.B69SL2
public import CFSG.Quasithin.H13.NQRigidWMGroups
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.Quasithin.Background.InternalSecB56M

public section

namespace CFSG.Quasithin.SmithD321

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.InternalSec
open scoped Matrix

section Group

variable {Ω : Type} [Group Ω]

private theorem commute_of_inf_eq_bot {M N : Subgroup Ω}
    (hMN : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) (hNM : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N)
    (hinf : M ⊓ N = ⊥) {m n : Ω} (hm : m ∈ M) (hn : n ∈ N) : m * n = n * m := by
  have h1 : m * n * m⁻¹ * n⁻¹ ∈ M := by
    have := M.mul_mem hm (hMN n hn m⁻¹ (M.inv_mem hm))
    simpa [mul_assoc] using this
  have h2 : m * n * m⁻¹ * n⁻¹ ∈ N := N.mul_mem (hNM m hm n hn) (N.inv_mem hn)
  have h3 : m * n * m⁻¹ * n⁻¹ = 1 := by
    have h4 : m * n * m⁻¹ * n⁻¹ ∈ M ⊓ N := ⟨h1, h2⟩
    rw [hinf] at h4
    exact h4
  calc m * n = m * n * m⁻¹ * n⁻¹ * (n * m) := by group
    _ = n * m := by rw [h3, one_mul]

private theorem inf_eq_bot_or_le {X S : Subgroup Ω} [IsSimpleGroup ↥X]
    (hS : ∀ x ∈ X, ∀ s ∈ S, x * s * x⁻¹ ∈ S) : S ⊓ X = ⊥ ∨ X ≤ S := by
  have hn : ((S ⊓ X).subgroupOf X).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact ⟨hS g g.2 a ha.1, X.mul_mem (X.mul_mem g.2 ha.2) (X.inv_mem g.2)⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((S ⊓ X).subgroupOf X) with h | h
  · left
    rw [eq_bot_iff]
    intro s hs
    have h1 : (⟨s, hs.2⟩ : ↥X) ∈ (S ⊓ X).subgroupOf X := hs
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
  · right
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥X) ∈ (S ⊓ X).subgroupOf X := by rw [h]; trivial
    exact h1.1

private theorem le_or_le_of_normal {X Y N : Subgroup Ω} [IsSimpleGroup ↥X] [IsSimpleGroup ↥Y]
    (hcomm : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a)
    (hZX : ∀ x ∈ X, (∀ y ∈ X, x * y = y * x) → x = 1)
    (hZY : ∀ x ∈ Y, (∀ y ∈ Y, x * y = y * x) → x = 1)
    (hNH : N ≤ X ⊔ Y) (hN : ∀ h ∈ X ⊔ Y, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hne : N ≠ ⊥) :
    X ≤ N ∨ Y ≤ N := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hX, hY⟩ := hcon
  have hX' := (inf_eq_bot_or_le (X := X) (S := N) fun x hx n hn =>
    hN x (le_sup_left (a := X) (b := Y) hx) n hn).resolve_right hX
  have hY' := (inf_eq_bot_or_le (X := Y) (S := N) fun x hx n hn =>
    hN x (le_sup_right (a := X) (b := Y) hx) n hn).resolve_right hY
  have hcomm' : ∀ a ∈ Y, ∀ b ∈ X, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hXn := conj_mem_of_mem_sup_of_commute hcomm
  have hYn : ∀ x ∈ X ⊔ Y, ∀ g ∈ Y, x * g * x⁻¹ ∈ Y := by
    rw [sup_comm]
    exact conj_mem_of_mem_sup_of_commute hcomm'
  apply hne
  rw [eq_bot_iff]
  intro n hn
  have cX : ∀ x ∈ X, x * n = n * x := fun x hx =>
    commute_of_inf_eq_bot (M := X) (N := N) (fun n' hn' x' hx' => hXn n' (hNH hn') x' hx')
      (fun x' hx' n' hn' => hN x' (le_sup_left (a := X) (b := Y) hx') n' hn')
      (by rw [inf_comm]; exact hX') hx hn
  have cY : ∀ x ∈ Y, x * n = n * x := fun x hx =>
    commute_of_inf_eq_bot (M := Y) (N := N) (fun n' hn' x' hx' => hYn n' (hNH hn') x' hx')
      (fun x' hx' n' hn' => hN x' (le_sup_right (a := X) (b := Y) hx') n' hn')
      (by rw [inf_comm]; exact hY') hx hn
  obtain ⟨x, hx, y, hy, rfl⟩ :=
    (B19Aux.mem_sup_iff_of_le_normalizer (le_normalizer_of_commute hcomm)).1 (hNH hn)
  have hx1 : x = 1 := hZX x hx fun x' hx' => by
    have h1 := cX x' hx'
    have h2 := hcomm x' hx' y hy
    calc x * x' = x * (x' * y) * y⁻¹ := by group
      _ = x * (y * x') * y⁻¹ := by rw [h2]
      _ = (x * y) * x' * y⁻¹ := by group
      _ = x' * (x * y) * y⁻¹ := by rw [← h1]
      _ = x' * x := by group
  subst hx1
  have hy1 : y = 1 := hZY y hy fun y' hy' => by
    have h1 := cY y' hy'
    rw [one_mul] at h1
    exact h1.symm
  rw [hy1, one_mul]
  exact Subgroup.one_mem _

private theorem not_isPGroup_two {X : Subgroup Ω} [IsSimpleGroup ↥X] [Finite ↥X]
    (hZX : ∀ x ∈ X, (∀ y ∈ X, x * y = y * x) → x = 1) : ¬ IsPGroup 2 ↥X := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt := h2.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center ↥X))
  apply hz
  have h1 : ((z : ↥X) : Ω) = 1 := hZX _ (z : ↥X).2 fun y hy => by
    have := Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm
  exact Subtype.ext (Subtype.ext h1)

end Group

section Pair

variable {I : Type} [CommGroup I]

private structure Pair (H X Y : Subgroup (MulAut I)) : Prop where
  sup : X ⊔ Y = H
  comm : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a
  simpleX : IsSimpleGroup ↥X
  simpleY : IsSimpleGroup ↥Y
  ncX : ∃ a b : ↥X, a * b ≠ b * a
  ncY : ∃ a b : ↥Y, a * b ≠ b * a
  irr : ∀ W : Subgroup I, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤
  redX : ∃ W : Subgroup I, (∀ x ∈ X, ∀ w ∈ W, x w ∈ W) ∧ W ≠ ⊥ ∧ W ≠ ⊤
  redY : ∃ W : Subgroup I, (∀ x ∈ Y, ∀ w ∈ W, x w ∈ W) ∧ W ≠ ⊥ ∧ W ≠ ⊤
  nffX : ∀ A : Subgroup (MulAut I), A ≤ X → A ≠ ⊥ → IsElemAbelian2 A →
    Nat.card ↥A * Nat.card ↥(fixV A) < Nat.card I
  nffY : ∀ A : Subgroup (MulAut I), A ≤ Y → A ≠ ⊥ → IsElemAbelian2 A →
    Nat.card ↥A * Nat.card ↥(fixV A) < Nat.card I
  card : 2 ^ 8 ≤ Nat.card I

variable {H X Y : Subgroup (MulAut I)}

private theorem Pair.swap (P : Pair H X Y) : Pair H Y X where
  sup := by rw [sup_comm]; exact P.sup
  comm := fun a ha b hb => (P.comm b hb a ha).symm
  simpleX := P.simpleY
  simpleY := P.simpleX
  ncX := P.ncY
  ncY := P.ncX
  irr := P.irr
  redX := P.redY
  redY := P.redX
  nffX := P.nffY
  nffY := P.nffX
  card := P.card

private theorem Pair.le_X (P : Pair H X Y) : X ≤ H := P.sup ▸ le_sup_left

private theorem Pair.le_Y (P : Pair H X Y) : Y ≤ H := P.sup ▸ le_sup_right

private theorem Pair.norm_X (P : Pair H X Y) : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X := by
  rw [← P.sup]
  exact conj_mem_of_mem_sup_of_commute P.comm

private theorem Pair.qX (P : Pair H X Y) : CFSG.IsQuasisimple ↥X := by
  have := P.simpleX
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup P.ncX).1

private theorem Pair.zX (P : Pair H X Y) : ∀ x ∈ X, (∀ y ∈ X, x * y = y * x) → x = 1 := by
  have := P.simpleX
  intro x hx hc
  have hZ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup P.ncX).2
  have h1 : (⟨x, hx⟩ : ↥X) ∈ Subgroup.center ↥X := Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (hc g g.2).symm
  rw [hZ, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1

private theorem Pair.ne_bot_X (P : Pair H X Y) : X ≠ ⊥ := by
  intro h
  obtain ⟨a, b, hab⟩ := P.ncX
  have h1 : ∀ c : ↥X, c = 1 := fun c => Subtype.ext ((Subgroup.eq_bot_iff_forall X).1 h c c.2)
  exact hab (by rw [h1 a, h1 b])

private theorem Pair.nontrivial [Finite I] (P : Pair H X Y) : Nontrivial I :=
  Finite.one_lt_card_iff_nontrivial.1 (lt_of_lt_of_le (by norm_num) P.card)

private theorem eq_one_of_forall_apply {x : MulAut I} (h : ∀ w, x w = w) : x = 1 :=
  MulEquiv.ext fun w => by rw [h w]; rfl

private theorem Pair.fixV_X (P : Pair H X Y) : fixV X = ⊥ := by
  have hinv : ∀ h ∈ H, ∀ w ∈ fixV X, h w ∈ fixV X := by
    intro h hh w hw
    refine mem_fixV.2 fun x hx => ?_
    have hx' : h⁻¹ * x * h ∈ X := by
      have := P.norm_X h⁻¹ (H.inv_mem hh) x hx
      simpa using this
    have e : x * h = h * (h⁻¹ * x * h) := by group
    calc x (h w) = (x * h) w := rfl
      _ = (h * (h⁻¹ * x * h)) w := by rw [e]
      _ = h ((h⁻¹ * x * h) w) := rfl
      _ = h w := by rw [mem_fixV.1 hw _ hx']
  rcases P.irr _ hinv with h | h
  · exact h
  · exfalso
    apply P.ne_bot_X
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    refine eq_one_of_forall_apply fun w => ?_
    have h1 : w ∈ fixV X := by rw [h]; trivial
    exact mem_fixV.1 h1 x hx

private theorem Pair.commV_X (P : Pair H X Y) : commV X = ⊤ := by
  have hinv : ∀ h ∈ H, ∀ w ∈ commV X, h w ∈ commV X := by
    intro h hh w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨x, hx, v, rfl⟩ := hw
      apply Subgroup.subset_closure
      refine ⟨h * x * h⁻¹, P.norm_X h hh x hx, h v, ?_⟩
      simp [MulAut.mul_apply, map_mul, map_inv]
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha
  rcases P.irr _ hinv with h | h
  · exfalso
    apply P.ne_bot_X
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    refine eq_one_of_forall_apply fun w => ?_
    have h1 : x w * w⁻¹ ∈ commV X := Subgroup.subset_closure ⟨x, hx, w, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact mul_inv_eq_one.1 h1
  · exact h

private theorem Pair.ncH (P : Pair H X Y) : ∃ a b : ↥H, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := P.ncX
  refine ⟨⟨a, P.le_X a.2⟩, ⟨b, P.le_X b.2⟩, fun h => hab (Subtype.ext ?_)⟩
  have h' := congrArg (Subtype.val : ↥H → MulAut I) h
  exact h'

private theorem Pair.isIrrSec [Finite I] (P : Pair H X Y) :
    XMod.IsIrrSec ↥H (⊥ : Subgroup I) ⊤ := by
  have := P.nontrivial
  exact ⟨bot_lt_top, fun J hJ _ _ => P.irr J ((isInv_iff H J).1 hJ)⟩

private theorem Pair.eq_one_of_commute [Finite I] (hI : ∀ v : I, v ^ 2 = 1) (P : Pair H X Y)
    {c : MulAut I} (hc : ∀ h ∈ H, c * h = h * c) {k : ℕ} (hk : c ^ 2 ^ k = 1) : c = 1 := by
  have hodd := InternalSec.odd_card_eqvAut_of_irr hI P.isIrrSec P.ncH
  have hce : c ∈ XMod.eqvAut ↥H I := by
    intro a p
    exact congrArg (fun f : MulAut I => f p) (hc a a.2)
  have hk' : (⟨c, hce⟩ : ↥(XMod.eqvAut ↥H I)) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(XMod.eqvAut ↥H I)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have hord := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
    (orderOf_dvd_natCard _)
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 hord)

end Pair

section Local

variable {I : Type} [CommGroup I] [Finite I] {H X Y : Subgroup (MulAut I)}

private theorem Pair.pCoreOf_eq_bot (hI : ∀ v : I, v ^ 2 = 1) (P : Pair H X Y)
    {G : Subgroup (MulAut I)} (hHG : H ≤ G) (hGH : G ≤ Subgroup.normalizer (H : Set (MulAut I))) :
    pCoreOf 2 G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥(pCoreOf 2 G) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  have hPG : pCoreOf 2 G ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
  have hHn : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H := fun g hg h hh =>
    (Subgroup.mem_normalizer_iff.1 (hGH hg) h).1 hh
  have hinf : pCoreOf 2 G ⊓ H = ⊥ := by
    by_contra hne
    have := P.simpleX
    have := P.simpleY
    have hN : ∀ h ∈ X ⊔ Y, ∀ n ∈ pCoreOf 2 G ⊓ H, h * n * h⁻¹ ∈ pCoreOf 2 G ⊓ H := by
      rw [P.sup]
      intro h hh n hn
      exact ⟨B1Red.conj_mem_pCoreOf (hHG hh) hn.1, H.mul_mem (H.mul_mem hh hn.2) (H.inv_mem hh)⟩
    rcases le_or_le_of_normal P.comm P.zX P.swap.zX (inf_le_right.trans P.sup.ge) hN hne with
      h | h
    · exact not_isPGroup_two P.zX (hP2.to_le (h.trans inf_le_left))
    · exact not_isPGroup_two P.swap.zX (hP2.to_le (h.trans inf_le_left))
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨k, hk⟩ := hP2 ⟨q, hq⟩
  have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine Subgroup.mem_bot.2 (P.eq_one_of_commute hI (fun h hh => ?_) hk')
  exact commute_of_inf_eq_bot (M := pCoreOf 2 G) (N := H)
    (fun n hn m hm => B1Red.conj_mem_pCoreOf (hHG hn) hm)
    (fun m hm n hn => hHn m (hPG hm) n hn) hinf hq hh

omit [Finite I] in
private theorem exists_offender {G : Subgroup (MulAut I)} (h : ffJ G ≠ ⊥) :
    ∃ A, IsFFStarOffender G A := by
  by_contra hno
  push Not at hno
  apply h
  unfold ffJ
  exact iSup₂_eq_bot.2 fun A hA => (hno A hA).elim

private theorem Pair.inf_ne_bot (hI : ∀ v : I, v ^ 2 = 1) (P : Pair H X Y)
    {G : Subgroup (MulAut I)} (hHG : H ≤ G) (hGH : G ≤ Subgroup.normalizer (H : Set (MulAut I)))
    (hJne : ffJ G ≠ ⊥) : ffJ G ⊓ H ≠ ⊥ := by
  intro hinf
  obtain ⟨A, hA⟩ := exists_offender hJne
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.2.1
  have ha2 : (a : MulAut I) ^ 2 ^ 1 = 1 := by rw [pow_one]; exact hA.2.2.1.2 a a.2
  apply ha
  refine Subtype.ext (P.eq_one_of_commute hI (fun h hh => ?_) ha2)
  have hJG := B6.ffJ_le G
  have hJn := B6.le_normalizer_ffJ G
  exact commute_of_inf_eq_bot (M := ffJ G) (N := H)
    (fun n hn m hm => (Subgroup.mem_normalizer_iff.1 (hJn (hHG hn)) m).1 hm)
    (fun m hm n hn => (Subgroup.mem_normalizer_iff.1 (hGH (hJG hm)) n).1 hn) hinf
    (B6.le_ffJ hA a.2) hh

omit [Finite I] in
private theorem quot_clause {G J : Subgroup (MulAut I)} (hsec : IsQuotientOfSQTKTC ↥G)
    (hJG : J ≤ G) : ∃ (X : Type) (_ : Group X) (_ : Finite X) (N : Subgroup X) (_ : N.Normal),
      SQTKGroup X ∧ Nonempty (↥J ≃* X ⧸ N) := by
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := hsec
  have hS : SQTKGroup S := ⟨hSQT, hK⟩
  set Q : Subgroup S := (J.subgroupOf G).comap φ with hQ
  let f : ↥Q →* ↥J :=
    { toFun := fun s =>
        ⟨((φ s : ↥G) : MulAut I), Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 s.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    rintro ⟨j, hj⟩
    obtain ⟨s, hs⟩ := hφ ⟨j, hJG hj⟩
    refine ⟨⟨s, ?_⟩, ?_⟩
    · show φ s ∈ J.subgroupOf G
      rw [hs]
      exact hj
    · apply Subtype.ext
      show ((φ s : ↥G) : MulAut I) = j
      rw [hs]
  exact ⟨↥Q, inferInstance, inferInstance, f.ker, inferInstance,
    InternalSec.sqtkGroup_subgroup hS Q, ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm⟩⟩

private theorem card_sup_le (A B : Subgroup I) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card ↥A * Nat.card ↥B := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective
    (fun p : ↥A × ↥B => (⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(A ⊔ B))) ?_
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
  exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩

end Local

section Cases

variable {I : Type} [CommGroup I] [Finite I] {H X Y : Subgroup (MulAut I)}

private theorem Pair.false_of_case245 (P : Pair H X Y) {J : Subgroup (MulAut I)} (hXJ : X ≤ J)
    (h : B56Case2 J ∨ B56Case4 J ∨ B56Case5 J) : False := by
  have hfix : fixV J = ⊥ := le_bot_iff.1 (P.fixV_X ▸ B1.fixV_le_fixV hXJ)
  have hcomm : commV J = ⊤ := top_le_iff.1 (P.commV_X ▸ commV_le_commV hXJ)
  rcases h with ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, t, -, -, -, -, -, hsupV, -, -, hcV₁, hcV₂, -⟩ |
      ⟨_, _, -, -, -, -, -, -, hidx, -⟩
  · exact not_le_perm_three P.qX hXJ e
  · rw [hfix, bot_sup_eq] at hsupV
    have h1 := card_sup_le (commV G₁) (commV G₂)
    rw [hsupV, Subgroup.card_top, hcV₂] at h1
    have h2 : Nat.card ↥(commV G₁) ≤ 2 ^ 5 := by
      rcases hcV₁ with h | h <;> simp [h]
    have h3 := P.card
    norm_num at h1 h2 h3
    omega
  · rw [hcomm, top_sup_eq, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)

private theorem Pair.false_of_le_top (P : Pair H X Y) {G J : Subgroup (MulAut I)}
    (hJG : J ≤ G) (hGH : G ≤ Subgroup.normalizer (H : Set (MulAut I))) (hHJ : H ≤ J)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) : False := by
  have hXJ : X ≤ J := P.le_X.trans hHJ
  have hYJ : Y ≤ J := P.le_Y.trans hHJ
  rcases hcases with h1 | h2 |
      ⟨G₁, G₂, -, -, -, -, -, W₁, W₂, hW₁, -, hinv₁, -, -, hWinf, hp₁, hp₂⟩ | h4 | h5
  · set E := quasithinGenFitting J with hEdef
    have hE : CFSG.IsQuasisimple ↥E := h1.1
    have hEJ : E ≤ J := quasithinGenFitting_le J
    have hEn : ∀ j ∈ J, ∀ e ∈ E, j * e * j⁻¹ ∈ E := fun j hj e he =>
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_quasithinGenFitting J hj) e).1 he
    have hEH : ∀ e ∈ E, ∀ h ∈ H, e * h * e⁻¹ ∈ H := fun e he h hh =>
      (Subgroup.mem_normalizer_iff.1 (hGH (hJG (hEJ he))) h).1 hh
    have hcent : ∀ {Z : Subgroup (MulAut I)}, Z ≤ J → (∀ z ∈ Z, ∀ e ∈ E, z * e = e * z) →
        Z ≤ E := fun hZJ hZ z hz => centralizer_quasithinGenFitting_le J
      ⟨hZJ hz, Subgroup.mem_centralizer_iff.2 fun e he => (hZ z hz e he).symm⟩
    by_cases hEle : E ≤ H
    · rcases le_or_le_of_commute hE (hEle.trans P.sup.ge) (fun g hg k hk => hEn g (hXJ hg) k hk)
          (fun g hg k hk => hEn g (hYJ hg) k hk) (fun k hk g hg => P.norm_X k (hEle hk) g hg)
          (fun k hk g hg => P.swap.norm_X k (hEle hk) g hg) with hEX | hEY
      · have hYE : Y ≤ E := hcent hYJ fun z hz e he => (P.comm e (hEX he) z hz).symm
        obtain ⟨a, b, hab⟩ := P.ncY
        exact hab (Subtype.ext (P.comm a (hEX (hYE a.2)) b b.2))
      · have hXE : X ≤ E := hcent hXJ fun z hz e he => P.comm z hz e (hEY he)
        obtain ⟨a, b, hab⟩ := P.ncX
        exact hab (Subtype.ext (P.comm a a.2 b (hEY (hXE b.2))))
    · have hc := B1Red.commute_of_normal_not_le (B1Red.isQuasisimple_to_open hE)
        (fun n hn l hl => hEn n (hHJ hn) l hl) hEH hEle
      have hHE : H ≤ E := hcent hHJ hc
      obtain ⟨a, b, hab⟩ := P.ncX
      exact hab (Subtype.ext (hc a (P.le_X a.2) b (hHE (P.le_X b.2))))
  · exact P.false_of_case245 hXJ (Or.inl h2)
  · rcases P.irr W₁ fun h hh w hw => (isInv_iff J W₁).1 hinv₁ h (hHJ hh) w hw with h | h
    · rw [h] at hW₁ hp₁
      rw [le_bot_iff.1 hW₁] at hp₁
      exact not_b56Piece_self hp₁
    · rw [h, top_inf_eq] at hWinf
      rw [hWinf] at hp₂
      exact not_b56Piece_self hp₂
  · exact P.false_of_case245 hXJ (Or.inr (Or.inl h4))
  · exact P.false_of_case245 hXJ (Or.inr (Or.inr h5))

private theorem Pair.false_of_not_le (P : Pair H X Y) {G J : Subgroup (MulAut I)} (hJG : J ≤ G)
    (hJn : ∀ g ∈ G, ∀ j ∈ J, g * j * g⁻¹ ∈ J) (hHG : H ≤ G)
    (hGH : G ≤ Subgroup.normalizer (H : Set (MulAut I))) (hXJ : X ≤ J) (hYJ : ¬ Y ≤ J)
    {A : Subgroup (MulAut I)} (hAJ : A ≤ J) (hA : A ≠ ⊥) (hAe : IsElemAbelian2 A)
    (hAc : Nat.card I ≤ Nat.card ↥A * Nat.card ↥(fixV A))
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) : False := by
  have := P.simpleY
  have hJY : J ⊓ Y = ⊥ := (inf_eq_bot_or_le (X := Y) (S := J) fun y hy j hj =>
    hJn y (hHG (P.le_Y hy)) j hj).resolve_right hYJ
  have hn : ∀ j ∈ J, ∀ x ∈ X, j * x * j⁻¹ ∈ X := by
    intro j hj x hx
    have h1 : j * x * j⁻¹ ∈ J := J.mul_mem (J.mul_mem hj (hXJ hx)) (J.inv_mem hj)
    have h2 : j * x * j⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 (hGH (hJG hj)) x).1 (P.le_X hx)
    rw [← P.sup] at h2
    obtain ⟨x', hx', y', hy', he⟩ :=
      (B19Aux.mem_sup_iff_of_le_normalizer (le_normalizer_of_commute P.comm)).1 h2
    have hy'J : y' ∈ J := by
      have e : y' = x'⁻¹ * (j * x * j⁻¹) := by rw [he]; group
      rw [e]
      exact J.mul_mem (J.inv_mem (hXJ hx')) h1
    have hy1 : y' = 1 := by
      have h3 : y' ∈ J ⊓ Y := ⟨hy'J, hy'⟩
      rw [hJY] at h3
      exact h3
    rw [he, hy1, mul_one]
    exact hx'
  have hfix : fixV X = ⊥ := P.fixV_X
  have hcomm : commV X = ⊤ := P.commV_X
  rcases hcases with h1 | h2 |
      ⟨G₁, G₂, hsup, -, hc, -, -, W₁, W₂, -, -, -, -, -, hWinf, hp₁, hp₂⟩ | h4 | h5
  · have hF := eq_of_le_quasisimple hXJ hn P.qX h1.1
    have hB := h1.2.1
    rw [hF] at hB
    rcases hB.1.2 with ⟨hirr, -, -⟩ | ⟨hJX, -⟩ | ⟨_, hJX, -⟩ | ⟨hJX, -⟩
    · rw [hcomm] at hirr
      obtain ⟨-, -, -, hmax⟩ := mem_irrPlus_top_iff.1 hirr
      obtain ⟨W, hW, hW0, hWt⟩ := P.redX
      rcases hmax W hW (by rw [hfix, inf_bot_eq]; exact bot_le) le_top with h | h
      · rw [hfix, inf_bot_eq] at h
        exact hW0 h
      · exact hWt h
    all_goals exact absurd hAc (not_le.2 (P.nffX A (hJX ▸ hAJ) hA hAe))
  · exact P.false_of_case245 hXJ (Or.inl h2)
  · have htop : ∀ {Z : Subgroup (MulAut I)}, X ≤ Z → commV Z = ⊤ := fun h =>
      top_le_iff.1 (hcomm ▸ commV_le_commV h)
    rcases le_or_le_of_sup_eq hsup hc hXJ hn P.qX with h | h
    · have hW₁ : W₁ = ⊤ := top_le_iff.1 ((htop h).symm.le.trans (commV_le_of_b56Piece hp₁))
      rw [hW₁, top_inf_eq] at hWinf
      rw [hWinf] at hp₂
      exact not_b56Piece_self hp₂
    · have hW₂ : W₂ = ⊤ := top_le_iff.1 ((htop h).symm.le.trans (commV_le_of_b56Piece hp₂))
      rw [hW₂, inf_top_eq] at hWinf
      rw [hWinf] at hp₁
      exact not_b56Piece_self hp₁
  · exact P.false_of_case245 hXJ (Or.inr (Or.inl h4))
  · exact P.false_of_case245 hXJ (Or.inr (Or.inr h5))

end Cases

section Main

variable {I : Type} [CommGroup I] [Finite I] {H X Y : Subgroup (MulAut I)}

private theorem Pair.not_isFFModule (h56 : AsB56) (hI : ∀ v : I, v ^ 2 = 1) (P : Pair H X Y)
    {G : Subgroup (MulAut I)} (hHG : H ≤ G) (hGH : G ≤ Subgroup.normalizer (H : Set (MulAut I)))
    (hsec : IsQuotientOfSQTKTC ↥G) : ¬ IsFFModule G := by
  intro hFF
  have hJne : ffJ G ≠ ⊥ := ffJ_ne_bot_of_isFFModule hI hFF
  have hJG : ffJ G ≤ G := B6.ffJ_le G
  have hJN := B6.le_normalizer_ffJ G
  have hJn : ∀ g ∈ G, ∀ j ∈ ffJ G, g * j * g⁻¹ ∈ ffJ G := fun g hg j hj =>
    (Subgroup.mem_normalizer_iff.1 (hJN hg) j).1 hj
  have hB53 : B53Hyp (ffJ G) := by
    refine ⟨?_, (ffJ_ffJ G).symm, quot_clause hsec hJG⟩
    have hJn' : ((ffJ G).subgroupOf G).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hJG).2 hJN
    have h := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 (ffJ G) G
      hJG hJn'
    rw [P.pCoreOf_eq_bot hI hHG hGH] at h
    exact le_bot_iff.1 h
  have hcases := h56 I hI (ffJ G) hJne hB53
  obtain ⟨A, hA⟩ := exists_offender hJne
  have hAJ : A ≤ ffJ G := B6.le_ffJ hA
  have hAc : Nat.card I ≤ Nat.card ↥A * Nat.card ↥(fixV A) := by
    have h := hA.2.2.2 ⊥ bot_le
    rwa [Subgroup.card_bot, one_mul, B1.fixV_bot, Subgroup.card_top] at h
  have := P.simpleX
  have := P.simpleY
  have hN : ∀ h ∈ X ⊔ Y, ∀ n ∈ ffJ G ⊓ H, h * n * h⁻¹ ∈ ffJ G ⊓ H := by
    rw [P.sup]
    intro h hh n hn
    exact ⟨hJn h (hHG hh) n hn.1, H.mul_mem (H.mul_mem hh hn.2) (H.inv_mem hh)⟩
  rcases le_or_le_of_normal P.comm P.zX P.swap.zX (inf_le_right.trans P.sup.ge) hN
      (P.inf_ne_bot hI hHG hGH hJne) with h | h
  · have hXJ : X ≤ ffJ G := h.trans inf_le_left
    by_cases hYJ : Y ≤ ffJ G
    · exact P.false_of_le_top hJG hGH (P.sup ▸ sup_le hXJ hYJ) hcases
    · exact P.false_of_not_le hJG hJn hHG hGH hXJ hYJ hAJ hA.2.1 hA.2.2.1 hAc hcases
  · have hYJ : Y ≤ ffJ G := h.trans inf_le_left
    by_cases hXJ : X ≤ ffJ G
    · exact P.false_of_le_top hJG hGH (P.sup ▸ sup_le hXJ hYJ) hcases
    · exact P.swap.false_of_not_le hJG hJn hHG hGH hYJ hXJ hAJ hA.2.1 hA.2.2.1 hAc hcases

end Main

section Model

variable {I : Type} [CommGroup I] {H : Subgroup (MulAut I)} {d : ℕ} {K : Type} [Field K]

private structure TD (H : Subgroup (MulAut I)) (d : ℕ) (K : Type) [Field K] where
  π : ↥(StatedSL d K) × ↥(StatedSL d K) →* ↥H
  e : I ≃* Multiplicative (Matrix (Fin d) (Fin d) K)
  surj : Function.Surjective π
  act : ∀ γ v, e ((π γ : MulAut I) v) = tensorAct d K γ (e v)

private noncomputable def topQuot (M : Type) [CommGroup M] :
    ↥(⊤ : Subgroup M) ⧸ (⊥ : Subgroup M).subgroupOf ⊤ ≃* M :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf ⊤)).trans
    (QuotientGroup.quotientBot.trans Subgroup.topEquiv)

private theorem topQuot_mk (M : Type) [CommGroup M] (m : ↥(⊤ : Subgroup M)) :
    topQuot M (QuotientGroup.mk m) = (m : M) :=
  rfl

private theorem nonempty_td (h : (FFModel.tensorNat d K).Realizes H ⊤ ⊥) :
    Nonempty (TD H d K) := by
  obtain ⟨π₀, hs₀, -, -, -, -, -, -, β₀, hβs₀, hβk₀, hβe₀⟩ := h
  set M := Multiplicative (Matrix (Fin d) (Fin d) K)
  let π : ↥(StatedSL d K) × ↥(StatedSL d K) →* ↥H := π₀
  have hs : Function.Surjective π := hs₀
  let β : ↥(⊤ : Subgroup I) →* (↥(⊤ : Subgroup M) ⧸ (⊥ : Subgroup M).subgroupOf ⊤) := β₀
  have hβs : Function.Surjective β := hβs₀
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk₀ u).mp hu))
  let e : I ≃* M := Subgroup.topEquiv.symm.trans
    ((MulEquiv.ofBijective β ⟨hinj, hβs⟩).trans (topQuot M))
  refine ⟨⟨π, e, hs, fun γ v => ?_⟩⟩
  have hm : β ⟨v, trivial⟩ = QuotientGroup.mk (⟨e v, trivial⟩ : ↥(⊤ : Subgroup M)) := by
    apply (topQuot M).injective
    rw [topQuot_mk]
    rfl
  have h1 : β ⟨(π γ : MulAut I) v, trivial⟩ =
      QuotientGroup.mk (⟨tensorAct d K γ (e v), trivial⟩ : ↥(⊤ : Subgroup M)) :=
    hβe₀ γ ⟨v, trivial⟩ ⟨e v, trivial⟩ trivial trivial hm
  have h2 : e ((π γ : MulAut I) v) = topQuot M (β ⟨(π γ : MulAut I) v, trivial⟩) := rfl
  rw [h2, h1, topQuot_mk]

private def TD.ι₁ (D : TD H d K) : ↥(StatedSL d K) →* MulAut I :=
  H.subtype.comp (D.π.comp (MonoidHom.inl _ _))

private def TD.ι₂ (D : TD H d K) : ↥(StatedSL d K) →* MulAut I :=
  H.subtype.comp (D.π.comp (MonoidHom.inr _ _))

private theorem TD.act₁ (D : TD H d K) (g : ↥(StatedSL d K)) (v : I) :
    D.e (D.ι₁ g v) = Multiplicative.ofAdd
      (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * Multiplicative.toAdd (D.e v)) := by
  have h := D.act (g, 1) v
  rw [show (D.π (g, 1) : MulAut I) = D.ι₁ g from rfl] at h
  rw [h]
  simp [tensorAct]

private theorem TD.act₂ (D : TD H d K) (g : ↥(StatedSL d K)) (v : I) :
    D.e (D.ι₂ g v) = Multiplicative.ofAdd
      (Multiplicative.toAdd (D.e v) * ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ) := by
  have h := D.act (1, g) v
  rw [show (D.π (1, g) : MulAut I) = D.ι₂ g from rfl] at h
  rw [h]
  simp [tensorAct]

private def transp : Multiplicative (Matrix (Fin d) (Fin d) K) ≃*
    Multiplicative (Matrix (Fin d) (Fin d) K) :=
  AddEquiv.toMultiplicative (Matrix.transposeAddEquiv (Fin d) (Fin d) K)

private def TD.swap (D : TD H d K) : TD H d K where
  π := D.π.comp (MulEquiv.prodComm : _ ≃* _).toMonoidHom
  e := D.e.trans transp
  surj γ := by
    obtain ⟨x, hx⟩ := D.surj γ
    exact ⟨x.swap, hx⟩
  act γ v := by
    have h := D.act (γ.2, γ.1) v
    change transp (D.e ((D.π (γ.2, γ.1) : MulAut I) v)) = _
    rw [h]
    simp only [tensorAct, transp, AddEquiv.toMultiplicative_apply_apply]
    simp [Matrix.transpose_mul, mul_assoc]

private theorem TD.inj₁ (D : TD H d K) : Function.Injective D.ι₁ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h := D.act₁ g (D.e.symm (Multiplicative.ofAdd 1))
  simp only [hg, MulAut.one_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd, mul_one] at h
  apply Subtype.ext
  apply Units.ext
  have h' := congrArg Multiplicative.toAdd h
  simpa using h'.symm

private theorem TD.inj₂ (D : TD H d K) : Function.Injective D.ι₂ := D.swap.inj₁

private theorem TD.sup (D : TD H d K) : D.ι₁.range ⊔ D.ι₂.range = H := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨g, rfl⟩
      exact (D.π (g, 1)).2
    · rintro _ ⟨g, rfl⟩
      exact (D.π (1, g)).2
  · intro h hh
    obtain ⟨γ, hγ⟩ := D.surj ⟨h, hh⟩
    have e : h = D.ι₁ γ.1 * D.ι₂ γ.2 := by
      have h1 : D.π γ = D.π (γ.1, 1) * D.π (1, γ.2) := by
        rw [← map_mul]
        congr 1
        exact Prod.ext (by simp) (by simp)
      have h2 := congrArg Subtype.val hγ
      rw [h1] at h2
      exact h2.symm
    rw [e]
    exact Subgroup.mul_mem_sup ⟨γ.1, rfl⟩ ⟨γ.2, rfl⟩

private theorem TD.comm (D : TD H d K) :
    ∀ a ∈ D.ι₁.range, ∀ b ∈ D.ι₂.range, a * b = b * a := by
  rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
  have e1 : ((g, 1) : ↥(StatedSL d K) × ↥(StatedSL d K)) * (1, h) = (1, h) * (g, 1) :=
    Prod.ext (by simp) (by simp)
  show ((D.π (g, 1) : ↥H) : MulAut I) * D.π (1, h) = D.π (1, h) * D.π (g, 1)
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, e1]

private noncomputable def tv {i j : Fin d} (hij : i ≠ j) (c : K) : ↥(StatedSL d K) :=
  specialLinearGroupEquivStatedSL d K
    ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij c⟩

private theorem tv_coe {i j : Fin d} (hij : i ≠ j) (c : K) :
    ((tv hij c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = Matrix.transvection i j c :=
  specialLinearGroupEquivStatedSL_coe d K _

private theorem TD.nc₁ (D : TD H d K) (hd : 2 ≤ d) : ∃ a b : ↥D.ι₁.range, a * b ≠ b * a := by
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
  obtain ⟨i, j, hij⟩ := exists_pair_ne (Fin d)
  refine ⟨⟨D.ι₁ (tv hij 1), tv hij 1, rfl⟩, ⟨D.ι₁ (tv hij.symm 1), tv hij.symm 1, rfl⟩,
    fun h => ?_⟩
  have h1 : D.ι₁ (tv hij 1 * tv hij.symm 1) = D.ι₁ (tv hij.symm 1 * tv hij 1) := by
    rw [map_mul, map_mul]
    exact congrArg Subtype.val h
  have h2 := congrArg (fun g : ↥(StatedSL d K) => ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    (D.inj₁ h1)
  simp only [Subgroup.coe_mul, Units.val_mul, tv_coe] at h2
  have h3 := congrFun (congrFun h2 i) i
  simp [Matrix.transvection, Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply, hij,
    hij.symm, mul_add, Finset.sum_add_distrib] at h3

private def TD.colSub (D : TD H d K) (j₀ : Fin d) : Subgroup I where
  carrier := {v | ∀ i j, j ≠ j₀ → Multiplicative.toAdd (D.e v) i j = 0}
  one_mem' := fun i j _ => by simp
  mul_mem' := fun {a b} ha hb i j hj => by
    simp [map_mul, toAdd_mul, ha i j hj, hb i j hj]
  inv_mem' := fun {a} ha i j hj => by
    simp [map_inv, toAdd_inv, ha i j hj]

private theorem TD.mem_colSub (D : TD H d K) {j₀ : Fin d} {v : I} :
    v ∈ D.colSub j₀ ↔ ∀ i j, j ≠ j₀ → Multiplicative.toAdd (D.e v) i j = 0 :=
  Iff.rfl

private theorem TD.red₁ (D : TD H d K) (hd : 2 ≤ d) :
    ∃ W : Subgroup I, (∀ x ∈ D.ι₁.range, ∀ w ∈ W, x w ∈ W) ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
  obtain ⟨j₀, j₁, hj⟩ := exists_pair_ne (Fin d)
  refine ⟨D.colSub j₀, ?_, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩ w hw
    refine D.mem_colSub.2 fun i j hj => ?_
    rw [D.act₁, toAdd_ofAdd, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => by rw [D.mem_colSub.1 hw k j hj, mul_zero]
  · intro h
    have hmem : D.e.symm (Multiplicative.ofAdd (Matrix.single j₀ j₀ (1 : K))) ∈ D.colSub j₀ := by
      refine D.mem_colSub.2 fun i j hj => ?_
      simp [Ne.symm hj]
    rw [h, Subgroup.mem_bot] at hmem
    have h1 := congrArg (fun v => Multiplicative.toAdd (D.e v)) hmem
    have h2 := congrFun (congrFun h1 j₀) j₀
    simp at h2
  · intro h
    have hmem : D.e.symm (Multiplicative.ofAdd (Matrix.single j₀ j₁ (1 : K))) ∈ D.colSub j₀ := by
      rw [h]
      trivial
    have h1 := D.mem_colSub.1 hmem j₀ j₁ hj.symm
    simp at h1

private theorem TD.card_eq (D : TD H d K) [Finite K] : Nat.card I = Nat.card K ^ (d * d) := by
  rw [Nat.card_congr D.e.toEquiv]
  show Nat.card (Fin d → Fin d → K) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin,
    ← pow_mul]

private theorem mem_of_closed (hd : 2 ≤ d) {S : Set (Matrix (Fin d) (Fin d) K)}
    (hadd : ∀ A ∈ S, ∀ B ∈ S, A + B ∈ S) (hneg : ∀ A ∈ S, -A ∈ S)
    (hmul : ∀ A ∈ S, ∀ B ∈ S, A * B ∈ S)
    (htr : ∀ i j : Fin d, i ≠ j → ∀ c : K, Matrix.transvection i j c ∈ S)
    (X : Matrix (Fin d) (Fin d) K) : X ∈ S := by
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
  obtain ⟨i₀, j₀, h₀⟩ := exists_pair_ne (Fin d)
  have h1 : (1 : Matrix (Fin d) (Fin d) K) ∈ S := by
    simpa [Matrix.transvection] using htr i₀ j₀ h₀ 0
  have h0 : (0 : Matrix (Fin d) (Fin d) K) ∈ S := by
    simpa using hadd 1 h1 (-1) (hneg 1 h1)
  have hoff : ∀ i j : Fin d, i ≠ j → ∀ c : K, Matrix.single i j c ∈ S := fun i j hij c => by
    simpa [Matrix.transvection] using hadd (-1) (hneg 1 h1) _ (htr i j hij c)
  have hsingle : ∀ (i j : Fin d) (c : K), Matrix.single i j c ∈ S := by
    intro i j c
    by_cases hij : i = j
    · subst hij
      obtain ⟨k, hk⟩ := exists_ne i
      have h2 := hmul _ (hoff i k (Ne.symm hk) c) _ (hoff k i hk 1)
      rwa [Matrix.single_mul_single_same, mul_one] at h2
    · exact hoff i j hij c
  rw [Matrix.matrix_eq_sum_single X]
  have hadd' : ∀ A B, A ∈ S → B ∈ S → A + B ∈ S := fun A B hA hB => hadd A hA B hB
  exact Finset.sum_induction _ (· ∈ S) hadd' h0 fun i _ =>
    Finset.sum_induction _ (· ∈ S) hadd' h0 fun j _ => hsingle i j _

private theorem TD.irr (D : TD H d K) (hd : 2 ≤ d) (W : Subgroup I)
    (hW : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  set S : Set (Matrix (Fin d) (Fin d) K) := {M | D.e.symm (Multiplicative.ofAdd M) ∈ W}
  have hSmem : ∀ M, M ∈ S ↔ D.e.symm (Multiplicative.ofAdd M) ∈ W := fun M => Iff.rfl
  have hSadd : ∀ M ∈ S, ∀ N ∈ S, M + N ∈ S := fun M hM N hN => by
    rw [hSmem, ofAdd_add, map_mul]
    exact W.mul_mem hM hN
  have hSneg : ∀ M ∈ S, -M ∈ S := fun M hM => by
    rw [hSmem, ofAdd_neg, map_inv]
    exact W.inv_mem hM
  have hS0 : (0 : Matrix (Fin d) (Fin d) K) ∈ S := by
    rw [hSmem, ofAdd_zero, map_one]
    exact W.one_mem
  have hL : ∀ g : ↥(StatedSL d K), ∀ M ∈ S,
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * M ∈ S := by
    intro g M hM
    have e1 : D.e.symm (Multiplicative.ofAdd (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * M))
        = D.ι₁ g (D.e.symm (Multiplicative.ofAdd M)) := by
      apply D.e.injective
      rw [MulEquiv.apply_symm_apply, D.act₁, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rw [hSmem, e1]
    exact hW _ (D.π (g, 1)).2 _ hM
  have hR : ∀ g : ↥(StatedSL d K), ∀ M ∈ S,
      M * ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ ∈ S := by
    intro g M hM
    have e1 : D.e.symm (Multiplicative.ofAdd (M * ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ))
        = D.ι₂ g (D.e.symm (Multiplicative.ofAdd M)) := by
      apply D.e.injective
      rw [MulEquiv.apply_symm_apply, D.act₂, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rw [hSmem, e1]
    exact hW _ (D.π (1, g)).2 _ hM
  have hT : ∀ A M, M ∈ S → A * M ∈ S := fun A => mem_of_closed (S := {A | ∀ M ∈ S, A * M ∈ S}) hd
    (fun A hA B hB M hM => by rw [add_mul]; exact hSadd _ (hA M hM) _ (hB M hM))
    (fun A hA M hM => by rw [neg_mul]; exact hSneg _ (hA M hM))
    (fun A hA B hB M hM => by rw [mul_assoc]; exact hA _ (hB M hM))
    (fun i j hij c M hM => by simpa [tv_coe] using hL (tv hij c) M hM) A
  have hT' : ∀ B M, M ∈ S → M * Bᵀ ∈ S := fun B => mem_of_closed (S := {B | ∀ M ∈ S, M * Bᵀ ∈ S})
    hd (fun A hA B hB M hM => by
      rw [Matrix.transpose_add, mul_add]
      exact hSadd _ (hA M hM) _ (hB M hM))
    (fun A hA M hM => by rw [Matrix.transpose_neg, mul_neg]; exact hSneg _ (hA M hM))
    (fun A hA B hB M hM => by rw [Matrix.transpose_mul, ← mul_assoc]; exact hA _ (hB M hM))
    (fun i j hij c M hM => by simpa [tv_coe] using hR (tv hij c) M hM) B
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  set M₀ := Multiplicative.toAdd (D.e w) with hM₀
  have hM₀S : M₀ ∈ S := by
    rw [hSmem, hM₀, ofAdd_toAdd, MulEquiv.symm_apply_apply]
    exact w.2
  have hM₀0 : M₀ ≠ 0 := by
    intro h
    apply hw1
    have h2 : D.e (w : I) = 1 := by
      have h3 : Multiplicative.ofAdd M₀ = D.e (w : I) := by rw [hM₀]; rfl
      rw [← h3, h]
      rfl
    apply Subtype.ext
    rw [OneMemClass.coe_one]
    exact D.e.injective (h2.trans (map_one D.e).symm)
  obtain ⟨k, l, hkl⟩ : ∃ k l, M₀ k l ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hM₀0 (Matrix.ext hcon)
  have hall : ∀ X, X ∈ S := by
    intro X
    rw [Matrix.matrix_eq_sum_single X]
    have hSadd' : ∀ A B, A ∈ S → B ∈ S → A + B ∈ S := fun A B hA hB => hSadd A hA B hB
    refine Finset.sum_induction _ (· ∈ S) hSadd' hS0 fun i _ =>
      Finset.sum_induction _ (· ∈ S) hSadd' hS0 fun j _ => ?_
    have h1 := hT' (Matrix.single j l (1 : K)) _
      (hT (Matrix.single i k (X i j * (M₀ k l)⁻¹)) _ hM₀S)
    rwa [Matrix.transpose_single, Matrix.single_mul_mul_single, mul_one, mul_assoc,
      inv_mul_cancel₀ hkl, mul_one] at h1
  rw [eq_top_iff]
  intro v _
  have h1 := hall (Multiplicative.toAdd (D.e v))
  rwa [hSmem, ofAdd_toAdd, MulEquiv.symm_apply_apply] at h1

end Model

section NotFF

variable {I : Type} [CommGroup I] {H : Subgroup (MulAut I)} {d : ℕ} {K : Type} [Field K]

private def fixVec (S : Subgroup ↥(StatedSL d K)) : AddSubgroup (Fin d → K) where
  carrier := {v | ∀ g ∈ S, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v = v}
  zero_mem' := fun g _ => Matrix.mulVec_zero _
  add_mem' := fun {a b} ha hb g hg => by rw [Matrix.mulVec_add, ha g hg, hb g hg]
  neg_mem' := fun {a} ha g hg => by rw [Matrix.mulVec_neg, ha g hg]

private theorem mem_fixVec {S : Subgroup ↥(StatedSL d K)} {v : Fin d → K} :
    v ∈ fixVec S ↔ ∀ g ∈ S, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v = v :=
  Iff.rfl

private theorem TD.card_comap (D : TD H d K) {A : Subgroup (MulAut I)} (hA : A ≤ D.ι₁.range) :
    Nat.card ↥(A.comap D.ι₁) = Nat.card ↥A := by
  conv_rhs => rw [← Subgroup.map_comap_eq_self hA]
  exact (Subgroup.card_map_of_injective D.inj₁).symm

private theorem TD.card_fixV_le (D : TD H d K) [Finite K] (A : Subgroup (MulAut I)) :
    Nat.card ↥(fixV A) ≤ Nat.card ↥(fixVec (A.comap D.ι₁)) ^ d := by
  have hcol : ∀ w ∈ fixV A, ∀ j : Fin d,
      (fun i => Multiplicative.toAdd (D.e w) i j) ∈ fixVec (A.comap D.ι₁) := by
    intro w hw j g hg
    have h1 : D.ι₁ g w = w := mem_fixV.1 hw _ hg
    have h2 := D.act₁ g w
    rw [h1] at h2
    funext i
    have h3 := congrFun (congrFun (congrArg Multiplicative.toAdd h2) i) j
    exact h3.symm
  let f : ↥(fixV A) → (Fin d → ↥(fixVec (A.comap D.ι₁))) := fun w j => ⟨_, hcol w w.2 j⟩
  have hf : Function.Injective f := by
    intro w w' h
    apply Subtype.ext
    apply D.e.injective
    have h1 : Multiplicative.toAdd (D.e w) = Multiplicative.toAdd (D.e w') := by
      ext i j
      exact congrFun (congrArg Subtype.val (congrFun h j)) i
    exact h1
  have h1 := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin] at h1

private theorem card_fixVec_le [Finite K] {S : Subgroup ↥(StatedSL d K)} {g : ↥(StatedSL d K)}
    (hg : g ∈ S) (hg1 : g ≠ 1) : Nat.card ↥(fixVec S) ≤ Nat.card K ^ (d - 1) := by
  set N := ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1 with hN
  have hN0 : N ≠ 0 := by
    intro h
    apply hg1
    apply Subtype.ext
    apply Units.ext
    simpa [hN, sub_eq_zero] using h
  obtain ⟨k, j, hkj⟩ : ∃ k j, N k j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hN0 (Matrix.ext hcon)
  have hfix : ∀ u ∈ fixVec S, N *ᵥ u = 0 := fun u hu => by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, (mem_fixVec.1 hu) g hg, sub_self]
  let f : ↥(fixVec S) → ({i : Fin d // i ≠ j} → K) := fun v i => (v : Fin d → K) i
  have hf : Function.Injective f := by
    intro v w hvw
    set u := (v : Fin d → K) - w with hu
    have hu0 : N *ᵥ u = 0 := hfix u (AddSubgroup.sub_mem _ v.2 w.2)
    have hoff : ∀ i, i ≠ j → u i = 0 := fun i hi => by
      have h1 := congrFun hvw ⟨i, hi⟩
      simp only [f] at h1
      simp [hu, h1]
    have hk := congrFun hu0 k
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j
      (fun i _ hi => by rw [hoff i hi, mul_zero]) (by simp)] at hk
    have huj : u j = 0 := (mul_eq_zero.1 hk).resolve_left hkj
    apply Subtype.ext
    funext i
    by_cases hi : i = j
    · subst hi
      exact sub_eq_zero.1 huj
    · exact sub_eq_zero.1 (hoff i hi)
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card {i : Fin d // i ≠ j} = d - 1 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rwa [Nat.card_fun, h2] at h1

private theorem TD.isPGroup_comap (D : TD H d K) {A : Subgroup (MulAut I)}
    (hAe : IsElemAbelian2 A) : IsPGroup 2 ↥(A.comap D.ι₁) := by
  intro g
  refine ⟨1, Subtype.ext (D.inj₁ ?_)⟩
  rw [pow_one, Subgroup.coe_pow, map_pow, OneMemClass.coe_one, map_one]
  exact hAe.2 _ g.2

private theorem card_statedSL_two [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥(StatedSL 2 K) = 2 ^ n * (4 ^ n - 1) := by
  have := Fintype.ofFinite K
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv, Matrix.card_SL_field,
    Fin.prod_univ_two]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  rw [← Nat.card_eq_fintype_card, hK]
  have h4 : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hpos : 0 < 2 ^ n - 1 := by
    have h := Finite.one_lt_card (α := K)
    rw [hK] at h
    omega
  have h1 : (2 ^ n) ^ 2 - 2 ^ n = 2 ^ n * (2 ^ n - 1) := by rw [Nat.mul_sub_one, sq]
  rw [h1, h4, show (4 ^ n - 1) * (2 ^ n * (2 ^ n - 1)) = 2 ^ n * (4 ^ n - 1) * (2 ^ n - 1) by
    ring, Nat.mul_div_cancel _ hpos]

private theorem card_statedSL_three_two : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

private theorem card_le_of_isPGroup_two [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    {S : Subgroup ↥(StatedSL 2 K)} (hS : IsPGroup 2 ↥S) : Nat.card ↥S ≤ 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS
  have hdvd : Nat.card ↥S ∣ 2 ^ n * (4 ^ n - 1) := by
    rw [← card_statedSL_two hK]
    exact Subgroup.card_subgroup_dvd_card S
  rw [hk] at hdvd ⊢
  have hodd : Odd (4 ^ n - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) ((Nat.even_pow' (by omega)).2 (by decide))
      odd_one
  have hcop : Nat.Coprime (2 ^ k) (4 ^ n - 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)

private theorem card_le_eight_of_isPGroup_two {S : Subgroup ↥(StatedSL 3 (ZMod 2))}
    (hS : IsPGroup 2 ↥S) : Nat.card ↥S ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS
  have hdvd : Nat.card ↥S ∣ 8 * 21 := by
    rw [show 8 * 21 = 168 by norm_num, ← card_statedSL_three_two]
    exact Subgroup.card_subgroup_dvd_card S
  rw [hk] at hdvd ⊢
  have hcop : Nat.Coprime (2 ^ k) 21 := Nat.Coprime.pow_left k (by norm_num)
  exact Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hdvd)

private theorem TD.exists_ne_one (D : TD H d K) {A : Subgroup (MulAut I)} (hAX : A ≤ D.ι₁.range)
    (hA : A ≠ ⊥) : ∃ g ∈ A.comap D.ι₁, g ≠ 1 := by
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA
  obtain ⟨g, hg⟩ := hAX a.2
  refine ⟨g, ?_, ?_⟩
  · show D.ι₁ g ∈ A
    rw [hg]
    exact a.2
  · rintro rfl
    apply ha
    apply Subtype.ext
    rw [← hg, map_one]
    rfl

private theorem TD.nff_two (D : TD H 2 K) [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 1 ≤ n) (A : Subgroup (MulAut I)) (hAX : A ≤ D.ι₁.range) (hA : A ≠ ⊥)
    (hAe : IsElemAbelian2 A) : Nat.card ↥A * Nat.card ↥(fixV A) < Nat.card I := by
  obtain ⟨g, hgS, hg1⟩ := D.exists_ne_one hAX hA
  have h1 := card_fixVec_le hgS hg1
  have h2 := D.card_fixV_le A
  have h3 := card_le_of_isPGroup_two hK hn (D.isPGroup_comap hAe)
  rw [D.card_comap hAX] at h3
  rw [hK] at h1
  rw [D.card_eq, hK]
  have h4 : Nat.card ↥(fixV A) ≤ (2 ^ n) ^ 2 :=
    h2.trans (Nat.pow_le_pow_left (by simpa using h1) 2)
  have h5 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  calc Nat.card ↥A * Nat.card ↥(fixV A) ≤ 2 ^ n * (2 ^ n) ^ 2 := Nat.mul_le_mul h3 h4
    _ = (2 ^ n) ^ 3 := by ring
    _ < (2 ^ n) ^ (2 * 2) := Nat.pow_lt_pow_right h5 (by norm_num)

open Matrix in
private theorem eq_one_of_mulVec_eq {n : ℕ} {R : Type*} [CommRing R]
    {M : Matrix (Fin n) (Fin n) R} (h : ∀ v, M *ᵥ v = v) : M = 1 := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  rw [mulVec_single_one] at h1
  simp only [col_apply] at h1
  rw [h1, one_apply, Pi.single_apply]

open Matrix in
private theorem card_le_four_of_fix {S : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))}
    {C : AddSubgroup (Fin 3 → ZMod 2)} (hC : 2 < Nat.card ↥C)
    (hfix : ∀ g ∈ S, ∀ v ∈ C, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v) :
    Nat.card ↥S ≤ 4 := by
  classical
  have hcard8 : Nat.card (Fin 3 → ZMod 2) = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  let Fix : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) → AddSubgroup (Fin 3 → ZMod 2) := fun g =>
    { carrier := {v | (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v}
      add_mem' := fun {a b} ha hb => by
        change (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (a + b) = a + b
        rw [mulVec_add, ha, hb]
      zero_mem' := by
        change (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ 0 = 0
        rw [mulVec_zero]
      neg_mem' := fun {a} ha => by
        change (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ a = a at ha
        have hneg : -a = a := funext fun i => ZMod.neg_eq_self_mod_two (a i)
        change (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (-a) = -a
        rw [hneg]
        exact ha }
  have hmemFix : ∀ g v, v ∈ Fix g ↔ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v :=
    fun _ _ => Iff.rfl
  have htriv : ∀ g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2), Fix g = ⊤ → g = 1 := by
    intro g hg
    have h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := eq_one_of_mulVec_eq fun v =>
      (hmemFix g v).1 (hg ▸ AddSubgroup.mem_top v)
    exact Units.ext h1
  have hdvd : ∀ D : AddSubgroup (Fin 3 → ZMod 2), Nat.card ↥D ∣ 8 := fun D =>
    hcard8 ▸ AddSubgroup.card_addSubgroup_dvd_card D
  have hC48 : Nat.card ↥C = 4 ∨ Nat.card ↥C = 8 := by
    have hCdvd := hdvd C
    have h8 : Nat.card ↥C ≤ 8 := Nat.le_of_dvd (by norm_num) hCdvd
    interval_cases h : Nat.card ↥C <;> simp_all
  have htop : ∀ D : AddSubgroup (Fin 3 → ZMod 2), 4 < Nat.card ↥D → D = ⊤ := by
    intro D hD
    have h8 : Nat.card ↥D ≤ 8 := Nat.le_of_dvd (by norm_num) (hdvd D)
    have hD8 : Nat.card ↥D = 8 := by
      have := hdvd D
      interval_cases h : Nat.card ↥D <;> simp_all
    exact AddSubgroup.eq_top_of_card_eq D (by rw [hD8, hcard8])
  rcases hC48 with h4 | h8
  ·
    have hCne : C ≠ ⊤ := fun h => by
      rw [h, AddSubgroup.card_top, hcard8] at h4
      norm_num at h4
    obtain ⟨e, he⟩ : ∃ e, e ∉ C := by
      by_contra hall
      push Not at hall
      exact hCne (eq_top_iff.2 fun v _ => hall v)
    have hinv : ∀ g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2), ∀ v,
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
          ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = v := by
      intro g v
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    let f : ↥S → {v : Fin 3 → ZMod 2 // v ∉ C} := fun g =>
      ⟨((g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e,
        fun hge => he (by
          have h1 := hfix _ (S.inv_mem g.2) _ hge
          rw [hinv] at h1
          rw [h1]
          exact hge)⟩
    have hf : Function.Injective f := by
      intro g h hgh
      have hval : ((g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e =
          ((h : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e := congrArg Subtype.val hgh
      set k : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
        (h : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))⁻¹ * g with hk
      have hkS : k ∈ S := S.mul_mem (S.inv_mem h.2) g.2
      have hke : e ∈ Fix k := by
        rw [hmemFix, hk, Units.val_mul, ← mulVec_mulVec, hval, hinv]
      have hCk : C ≤ Fix k := fun v hv => (hmemFix k v).2 (hfix k hkS v hv)
      have hlt : 4 < Nat.card ↥(Fix k) := by
        have hlt' : C < Fix k := lt_of_le_of_ne hCk fun hEq => he (hEq ▸ hke)
        rw [← h4]
        exact AddSubgroup.card_lt_of_lt hlt'
      have hk1 := htriv k (htop _ hlt)
      apply Subtype.ext
      have : (h : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))⁻¹ * g = 1 := hk1
      rw [inv_mul_eq_one] at this
      exact this.symm
    have hcompl : Nat.card {v : Fin 3 → ZMod 2 // v ∉ C} = 4 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card,
        hcard8, ← Nat.card_eq_fintype_card]
      rw [h4]
    calc Nat.card ↥S ≤ Nat.card {v : Fin 3 → ZMod 2 // v ∉ C} :=
          Nat.card_le_card_of_injective f hf
      _ = 4 := hcompl
  ·
    have hCt : C = ⊤ := AddSubgroup.eq_top_of_card_eq C (by rw [h8, hcard8])
    have hS : S = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      exact Subgroup.mem_bot.2 (htriv g (eq_top_iff.2 fun v _ =>
        (hmemFix g v).2 (hfix g hg v (hCt ▸ AddSubgroup.mem_top v))))
    rw [hS, Subgroup.card_bot]
    norm_num

private theorem TD.nff_three (D : TD H 3 (ZMod 2)) (A : Subgroup (MulAut I))
    (hAX : A ≤ D.ι₁.range) (hA : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    Nat.card ↥A * Nat.card ↥(fixV A) < Nat.card I := by
  obtain ⟨g, hgS, hg1⟩ := D.exists_ne_one hAX hA
  have h1 := card_fixVec_le hgS hg1
  rw [Nat.card_zmod] at h1
  norm_num at h1
  have h2 := D.card_fixV_le A
  have h3 := card_le_eight_of_isPGroup_two (D.isPGroup_comap hAe)
  rw [D.card_comap hAX] at h3
  rw [D.card_eq, Nat.card_zmod]
  norm_num
  by_cases hC : Nat.card ↥(fixVec (A.comap D.ι₁)) ≤ 2
  · have h4 : Nat.card ↥(fixV A) ≤ 8 := h2.trans (by
      calc Nat.card ↥(fixVec (A.comap D.ι₁)) ^ 3 ≤ 2 ^ 3 := Nat.pow_le_pow_left hC 3
        _ = 8 := by norm_num)
    calc Nat.card ↥A * Nat.card ↥(fixV A) ≤ 8 * 8 := Nat.mul_le_mul h3 h4
      _ < 512 := by norm_num
  · have h5 : Nat.card ↥(A.comap D.ι₁) ≤ 4 := by
      have h6 := card_le_four_of_fix (S := (A.comap D.ι₁).map (StatedSL 3 (ZMod 2)).subtype)
        (C := fixVec (A.comap D.ι₁)) (by omega) (by
          rintro _ ⟨x, hx, rfl⟩ v hv
          exact mem_fixVec.1 hv x hx)
      rwa [Subgroup.card_map_of_injective (StatedSL 3 (ZMod 2)).subtype_injective] at h6
    rw [D.card_comap hAX] at h5
    have h4 : Nat.card ↥(fixV A) ≤ 64 := h2.trans (by
      calc Nat.card ↥(fixVec (A.comap D.ι₁)) ^ 3 ≤ 4 ^ 3 := Nat.pow_le_pow_left h1 3
        _ = 64 := by norm_num)
    calc Nat.card ↥A * Nat.card ↥(fixV A) ≤ 4 * 64 := Nat.mul_le_mul h5 h4
      _ < 512 := by norm_num

end NotFF

section Final

variable {I : Type} [CommGroup I] {H : Subgroup (MulAut I)} {d : ℕ} {K : Type} [Field K]

private theorem TD.pair (D : TD H d K) (hd : 2 ≤ d) [IsSimpleGroup ↥(StatedSL d K)]
    (hnff : ∀ D' : TD H d K, ∀ A : Subgroup (MulAut I), A ≤ D'.ι₁.range → A ≠ ⊥ →
      IsElemAbelian2 A → Nat.card ↥A * Nat.card ↥(fixV A) < Nat.card I)
    (hcard : 2 ^ 8 ≤ Nat.card I) : Pair H D.ι₁.range D.ι₂.range where
  sup := D.sup
  comm := D.comm
  simpleX := (MonoidHom.ofInjective D.inj₁).symm.isSimpleGroup
  simpleY := (MonoidHom.ofInjective D.inj₂).symm.isSimpleGroup
  ncX := D.nc₁ hd
  ncY := D.swap.nc₁ hd
  irr := D.irr hd
  redX := D.red₁ hd
  redY := D.swap.red₁ hd
  nffX := hnff D
  nffY := hnff D.swap
  card := hcard

end Final

theorem not_isFFModule_tensor (h56 : AsB56) {I : Type} [CommGroup I] [Finite I]
    (hI : ∀ v : I, v ^ 2 = 1) {G H : Subgroup (MulAut I)}
    (hT : (∃ n, 2 ≤ n ∧ Omega4PlusModule H n) ∨ TensorNatL32 H)
    (hHG : H ≤ G) (hGH : G ≤ Subgroup.normalizer (H : Set (MulAut I)))
    (hsec : IsQuotientOfSQTKTC ↥G) : ¬ IsFFModule G := by
  rcases hT with ⟨n, hn, K, _, _, hK, hR⟩ | hR
  · obtain ⟨D⟩ := nonempty_td hR
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : IsSimpleGroup ↥(StatedSL 2 K) := H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
    have hcard : 2 ^ 8 ≤ Nat.card I := by
      rw [D.card_eq, hK, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact (D.pair le_rfl (fun D' => D'.nff_two hK (by omega)) hcard).not_isFFModule h56 hI hHG
      hGH hsec
  · obtain ⟨D⟩ := nonempty_td hR
    have : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) := B69.isSimpleGroup_statedSL_two (by simp) le_rfl
    have hcard : 2 ^ 8 ≤ Nat.card I := by
      rw [D.card_eq, Nat.card_zmod]
      norm_num
    exact (D.pair (by norm_num) (fun D' => D'.nff_three) hcard).not_isFFModule h56 hI hHG hGH hsec

end CFSG.Quasithin.SmithD321
