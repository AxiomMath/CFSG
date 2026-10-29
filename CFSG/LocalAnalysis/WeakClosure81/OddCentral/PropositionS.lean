module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.ChiefPrime
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.SectionLA
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.SectionModule
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.SectionImage
public import CFSG.CGT.T75H.Bender
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.Frame
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.MinimalCounterexample
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Timmesfeld.Bridge.Asc72

theorem frame_commute_hat {G M : Type} [Group G] [Finite G] [AddCommGroup M] [Finite M]
    [DistribMulAction G M] (hModd : Odd (Nat.card M))
    (hfaith : ∀ g : G, (∀ m : M, g • m = m) → g = 1)
    (hirr : ∀ N : AddSubgroup M, (∀ g : G, ∀ m ∈ N, g • m ∈ N) → N = ⊥ ∨ N = ⊤)
    {R : Subgroup G} [hRn : R.Normal] (hRodd : Odd (Nat.card R))
    {d : Fin 3 → G} {t : G} (hd : ∀ i, d i * d i = 1) (hdc : ∀ i j, d i * d j = d j * d i)
    (ht : ∀ i, t * d i * t⁻¹ = d (i + 1))
    (hcR : ∀ g : G, (d 0 * d 1 * d 2)⁻¹ * (g * (d 0 * d 1 * d 2) * g⁻¹) ∈ R)
    (hLAM : ∀ i j, i ≠ j → ∀ m : M, (d i * d j) • m = m → d i • m = m)
    (hgen : normalClosure ({d 0} : Set G) = ⊤)
    (hlift : ∀ Q Q₀ : Subgroup G, Q.Normal → Q₀.Normal → Q ≤ R → Q₀ ≤ Q →
      (∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Q₀) →
      (∀ N : Subgroup G, N.Normal → Q₀ ≤ N → N ≤ Q → N = Q₀ ∨ N = Q) →
      (∃ x ∈ Q, d 0 * x * (d 0)⁻¹ * x⁻¹ ∉ Q₀) →
      (∀ y ∈ R, ∀ x ∈ Q, (y * (d 0 * d 1 * d 2) * y⁻¹ * (d 0 * d 1 * d 2)⁻¹) * x *
        (y * (d 0 * d 1 * d 2) * y⁻¹ * (d 0 * d 1 * d 2)⁻¹)⁻¹ * x⁻¹ ∈ Q₀) ∧
      (∀ i j, i ≠ j → ∀ x ∈ Q, (d i * d j) * x * (d i * d j)⁻¹ * x⁻¹ ∈ Q₀ →
        d i * x * (d i)⁻¹ * x⁻¹ ∈ Q₀)) :
    ∀ i, ∀ y ∈ R, d i * y = y * d i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, y₀, hy₀, hne₀⟩ := hcon
  obtain ⟨r, hr, hrM, Q, Q₀, hQn, hQR, hQ₀Q, hQ', hQ₀Z, hQ₀p, hQr, hchief, hS1⟩ :=
    exists_S1 hfaith hirr hRodd hd ht hgen ⟨y₀, hy₀, i₀, hne₀⟩
  haveI := hQn
  haveI hQ₀n : Q₀.Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hQ₀Z hn) g, mul_inv_cancel_right]; exact hn⟩
  have hQodd : Odd (Nat.card Q) := Odd.of_dvd_nat hRodd (card_dvd_of_le hQR)
  have hdn : ∀ i j, i ≠ j → d i ≠ d j := by
    intro i j hij hdij
    have h1 : d i = 1 := hfaith _ fun m => hLAM i j hij m (by rw [← hdij, hd i, one_smul])
    have hrot : ∀ a, d a = 1 → d (a + 1) = 1 := fun a ha => by rw [← ht a, ha]; simp
    have hall : ∀ a, d a = 1 := by
      intro a
      have key : ∀ a b : Fin 3, a = b ∨ a = b + 1 ∨ a = b + 1 + 1 := by decide
      rcases key a i with rfl | rfl | rfl
      · exact h1
      · exact hrot _ h1
      · exact hrot _ (hrot _ h1)
    exact hne₀ (by rw [hall i₀, one_mul, mul_one])
  obtain ⟨hRc, hLAW⟩ := hlift Q Q₀ hQn hQ₀n hQR hQ₀Q hQ' hchief hS1
  exact false_of_propS_counterexample hr hrM hModd hfaith hirr hQ₀Q hQodd hQ' hQ₀Z hQ₀p hQr
    hchief hRodd hd hdc hdn ht hcR hRc hLAW hLAM hS1 hgen

section
variable {Y : Type} [Group Y]

@[expose] def secCent (A B : Subgroup Y) [hA : A.Normal] [hB : B.Normal] : Subgroup Y where
  carrier := {g | ∀ a ∈ A, g * a * g⁻¹ * a⁻¹ ∈ B}
  mul_mem' := fun {g h} hg hh a ha => by
    have h1 := hh a ha
    have h2 := hg a ha
    rw [show g * h * a * (g * h)⁻¹ * a⁻¹ = g * (h * a * h⁻¹ * a⁻¹) * g⁻¹ * (g * a * g⁻¹ * a⁻¹) by
      group]
    exact B.mul_mem (hB.conj_mem _ h1 g) h2
  one_mem' := fun a _ => by simp
  inv_mem' := fun {g} hg a ha => by
    have h := B.inv_mem (hg _ (show g⁻¹ * a * g ∈ A by simpa using hA.conj_mem a ha g⁻¹))
    convert h using 1
    group

instance secCent_normal (A B : Subgroup Y) [hA : A.Normal] [hB : B.Normal] :
    (secCent A B).Normal :=
  ⟨fun g hg h a ha => by
    have := hB.conj_mem _ (hg _ (show h⁻¹ * a * h ∈ A by simpa using hA.conj_mem a ha h⁻¹)) h
    convert this using 1
    group⟩

@[expose] def secSet (O A B : Subgroup Y) : Set Y :=
  {r | r ∈ O ∧ ∀ a ∈ A, r * a * r⁻¹ * a⁻¹ ∈ B}

theorem odd_card_fusionOddCore (H : Type) [Group H] [Finite H] :
    Odd (Nat.card (fusionOddCore H)) := by
  have e : fusionOddCore H = CFSG.pPrimeCore 2 H := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext N
    exact and_congr Iff.rfl Nat.coprime_two_left.symm
  rw [e]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

variable [Finite Y]

theorem comm_of_chief_odd {A B : Subgroup Y} [hA : A.Normal] [hB : B.Normal] (hBA : B < A)
    (hAodd : Odd (Nat.card A))
    (hmin : ∀ N : Subgroup Y, N.Normal → B ≤ N → N ≤ A → N = B ∨ N = A) :
    ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ B := by
  let f := QuotientGroup.mk' B
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective B
  have hfB : ∀ g, f g = 1 ↔ g ∈ B := fun g => QuotientGroup.eq_one_iff g
  haveI hAn : (A.map f).Normal := hA.map f hf
  have hsol : Group.IsSolvable (A.map f) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Odd.of_dvd_nat hAodd (card_map_dvd A f))
  have hne : A.map f ≠ ⊥ := by
    obtain ⟨a, ha, haB⟩ : ∃ a ∈ A, a ∉ B := by
      by_contra h; push Not at h; exact hBA.ne (le_antisymm hBA.le h)
    intro h
    have : f a ∈ A.map f := mem_map_of_mem f ha
    rw [h, mem_bot, hfB] at this
    exact haB this
  have hmin' : ∀ M' ≤ A.map f, M'.Normal → M' ≠ ⊥ → M' = A.map f := by
    intro M' hM' hM'n hM'1
    haveI := hM'n
    have hK := hmin (M'.comap f) inferInstance
      (fun b hb => by rw [mem_comap, (hfB b).mpr hb]; exact M'.one_mem)
      (fun k hk => by
        obtain ⟨a, ha, hak⟩ := hM' hk
        have : a⁻¹ * k ∈ B := (hfB _).mp (by rw [map_mul, map_inv, hak, inv_mul_cancel])
        rw [show k = a * (a⁻¹ * k) by group]
        exact A.mul_mem ha (hBA.le this))
    rcases hK with h | h
    · exfalso; apply hM'1
      rw [eq_bot_iff]
      intro m hm
      obtain ⟨k, rfl⟩ := hf m
      have : k ∈ M'.comap f := hm
      rw [h] at this
      rw [mem_bot, hfB]; exact this
    · refine le_antisymm hM' ?_
      rintro _ ⟨a, ha, rfl⟩
      have : a ∈ M'.comap f := by rw [h]; exact ha
      exact this
  intro a ha b hb
  have := CFSG.CGT.T75H.comm_of_minimal_normal le_rfl hsol hne hmin' (f a) (mem_map_of_mem f ha)
    (f b) (mem_map_of_mem f hb)
  rw [← hfB, map_mul, map_mul, map_mul, map_inv, map_inv, this]
  group

theorem propS_module {D : Set Y} (hD : IsOddTransp D)
    (hDc : ∀ x ∈ D, ∀ g : Y, g * x * g⁻¹ ∈ D) {O : Subgroup Y} [hOn : O.Normal]
    (hOodd : Odd (Nat.card O)) {d : Fin 3 → Y} {t : Y} (hdD : ∀ i, d i ∈ D)
    (hdc : ∀ i j, d i * d j = d j * d i) (hdn : ∀ i j, i ≠ j → d i ≠ d j)
    (ht : ∀ i, t * d i * t⁻¹ = d (i + 1))
    (hcO : ∀ g : Y, (d 0 * d 1 * d 2)⁻¹ * (g * (d 0 * d 1 * d 2) * g⁻¹) ∈ O)
    (hgen : normalClosure ({d 0} : Set Y) = ⊤)
    {A B : Subgroup Y} [hA : A.Normal] [hB : B.Normal]
    {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction Y M] (hModd : Odd (Nat.card M))
    (htriv : ∀ y : Y, (∀ m : M, y • m = m) ↔ ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ B)
    (hirrY : ∀ N : AddSubgroup M, (∀ y : Y, ∀ m ∈ N, y • m ∈ N) → N = ⊥ ∨ N = ⊤)
    (hLAY : ∀ i j, i ≠ j → ∀ m : M, (d i * d j) • m = m → d i • m = m)
    (hIH : ∀ A' B' : Subgroup Y, A'.Normal → B'.Normal → B' < A' → A' ≤ O →
      (∀ N : Subgroup Y, N.Normal → B' ≤ N → N ≤ A' → N = B' ∨ N = A') →
      secSet O A B ⊂ secSet O A' B' →
      ∀ i, ∀ r ∈ O, ∀ a ∈ A',
        (d i * r * (d i)⁻¹ * r⁻¹) * a * (d i * r * (d i)⁻¹ * r⁻¹)⁻¹ * a⁻¹ ∈ B') :
    ∀ i, ∀ r ∈ O, ∀ a ∈ A,
      (d i * r * (d i)⁻¹ * r⁻¹) * a * (d i * r * (d i)⁻¹ * r⁻¹)⁻¹ * a⁻¹ ∈ B := by
  classical
  have hd2 : ∀ i, d i * d i = 1 := fun i => by
    have := pow_orderOf_eq_one (d i); rw [hD.1 _ (hdD i), pow_two] at this; exact this
  have hρs := imgHom_surjective (Y := Y) (M := M)
  have hρ1 : ∀ y : Y, imgHom Y M y = 1 ↔ ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ B :=
    fun y => (imgHom_eq_one_iff y).trans (htriv y)
  have hcomm := frame_commute_hat (G := imgGroup Y M) (M := M) hModd img_faithful (img_irr hirrY)
    (R := O.map (imgHom Y M)) (hRn := hOn.map _ hρs) (Odd.of_dvd_nat hOodd (card_map_dvd O _))
    (d := fun i => imgHom Y M (d i)) (t := imgHom Y M t)
    (fun i => by rw [← map_mul, hd2 i, map_one])
    (fun i j => by simp only [← map_mul]; rw [hdc i j])
    (fun i => by simp only [← map_inv, ← map_mul]; rw [ht i])
    (fun g => by
      obtain ⟨g, rfl⟩ := hρs g
      exact ⟨_, hcO g, by simp only [map_mul, map_inv]⟩)
    (fun i j hij m hm => by
      rw [← map_mul] at hm
      exact hLAY i j hij m hm)
    (by
      rw [← Set.image_singleton, ← map_normalClosure _ _ hρs, hgen]
      exact map_top_of_surjective _ hρs)
    (by
      intro Q Q₀ hQn hQ₀n hQR hQ₀Q hQ' hchief hS1
      haveI := hQn
      haveI := hQ₀n
      let At : Subgroup Y := Q.comap (imgHom Y M) ⊓ O
      let Bt : Subgroup Y := Q₀.comap (imgHom Y M) ⊓ O
      haveI hAtn : At.Normal := inferInstance
      haveI hBtn : Bt.Normal := inferInstance
      have hAtodd : Odd (Nat.card At) := Odd.of_dvd_nat hOodd (card_dvd_of_le inf_le_right)
      have hBtAt : Bt ≤ At := fun y hy => ⟨hQ₀Q hy.1, hy.2⟩
      have hAtO : At ≤ O := inf_le_right
      obtain ⟨x₀, hx₀Q, hx₀⟩ := hS1
      obtain ⟨a₀, ha₀O, rfl⟩ := hQR hx₀Q
      have ha₀At : a₀ ∈ At := ⟨hx₀Q, ha₀O⟩
      have ha₀Bt : a₀ ∉ Bt := fun h => hx₀ (by
        have h1 : imgHom Y M a₀ ∈ Q₀ := h.1
        exact Q₀.mul_mem (hQ₀n.conj_mem _ h1 _) (Q₀.inv_mem h1))
      have hBtlt : Bt < At := lt_of_le_of_ne hBtAt fun h => ha₀Bt (h ▸ ha₀At)
      have hminT : ∀ N : Subgroup Y, N.Normal → Bt ≤ N → N ≤ At → N = Bt ∨ N = At := by
        intro N hN h1 h2
        haveI := hN
        have hNm : (N.map (imgHom Y M)).Normal := hN.map _ hρs
        have hQ₀N : Q₀ ≤ N.map (imgHom Y M) := fun q hq => by
          obtain ⟨a, haO, rfl⟩ := hQR (hQ₀Q hq)
          exact ⟨a, h1 ⟨hq, haO⟩, rfl⟩
        have hNQ : N.map (imgHom Y M) ≤ Q := by
          rintro _ ⟨n, hn, rfl⟩; exact (h2 hn).1
        rcases hchief _ hNm hQ₀N hNQ with h | h
        · left
          refine le_antisymm (fun n hn => ⟨?_, (h2 hn).2⟩) h1
          show imgHom Y M n ∈ Q₀
          rw [← h]; exact mem_map_of_mem _ hn
        · right
          refine le_antisymm h2 fun a ha => ?_
          have : imgHom Y M a ∈ N.map (imgHom Y M) := by rw [h]; exact ha.1
          obtain ⟨n, hn, hna⟩ := this
          have hk : n⁻¹ * a ∈ Bt := ⟨by
            show imgHom Y M (n⁻¹ * a) ∈ Q₀
            rw [map_mul, map_inv, hna, inv_mul_cancel]; exact Q₀.one_mem,
            O.mul_mem (O.inv_mem (h2 hn).2) ha.2⟩
          rw [show a = n * (n⁻¹ * a) by group]
          exact N.mul_mem hn (h1 hk)
      have hss : secSet O A B ⊂ secSet O At Bt := by
        rw [Set.ssubset_iff_of_subset]
        · refine ⟨a₀, ⟨ha₀O, fun a ha => ⟨?_, O.mul_mem (O.mul_mem (O.mul_mem ha₀O ha.2)
            (O.inv_mem ha₀O)) (O.inv_mem ha.2)⟩⟩, fun h => ?_⟩
          · show imgHom Y M (a₀ * a * a₀⁻¹ * a⁻¹) ∈ Q₀
            simp only [map_mul, map_inv]
            exact hQ' _ hx₀Q _ ha.1
          · have h1 : imgHom Y M a₀ = 1 := (hρ1 a₀).mpr h.2
            apply hx₀
            rw [h1]; simp
        · intro r hr
          refine ⟨hr.1, fun a ha => ⟨?_, O.mul_mem (O.mul_mem (O.mul_mem hr.1 ha.2)
            (O.inv_mem hr.1)) (O.inv_mem ha.2)⟩⟩
          have h1 : imgHom Y M r = 1 := (hρ1 r).mpr hr.2
          show imgHom Y M (r * a * r⁻¹ * a⁻¹) ∈ Q₀
          simp only [map_mul, map_inv, h1]
          simp
      have hT := hIH At Bt hAtn hBtn hBtlt hAtO hminT hss
      refine ⟨?_, ?_⟩
      · intro yh hyh x hx
        obtain ⟨y, hyO, rfl⟩ := hyh
        obtain ⟨a, haO, rfl⟩ := hQR hx
        have haAt : a ∈ At := ⟨hx, haO⟩
        have hdiC : ∀ i, ∀ r ∈ O, d i * r * (d i)⁻¹ * r⁻¹ ∈ secCent At Bt :=
          fun i r hr a ha => hT i r hr a ha
        have he : ∀ i, y * d i * y⁻¹ * (d i)⁻¹ ∈ secCent At Bt := fun i => by
          rw [show y * d i * y⁻¹ * (d i)⁻¹ = y * (d i * y⁻¹ * (d i)⁻¹ * y⁻¹⁻¹) * y⁻¹ by group]
          exact (secCent_normal At Bt).conj_mem _ (hdiC i y⁻¹ (O.inv_mem hyO)) y
        have hyc : y * (d 0 * d 1 * d 2) * y⁻¹ * (d 0 * d 1 * d 2)⁻¹ ∈ secCent At Bt := by
          rw [show y * (d 0 * d 1 * d 2) * y⁻¹ * (d 0 * d 1 * d 2)⁻¹ =
            (y * d 0 * y⁻¹ * (d 0)⁻¹) * (d 0 * (y * d 1 * y⁻¹ * (d 1)⁻¹) * (d 0)⁻¹) *
            ((d 0 * d 1) * (y * d 2 * y⁻¹ * (d 2)⁻¹) * (d 0 * d 1)⁻¹) by group]
          exact (secCent At Bt).mul_mem ((secCent At Bt).mul_mem (he 0)
            ((secCent_normal At Bt).conj_mem _ (he 1) _))
            ((secCent_normal At Bt).conj_mem _ (he 2) _)
        have h2 : imgHom Y M ((y * (d 0 * d 1 * d 2) * y⁻¹ * (d 0 * d 1 * d 2)⁻¹) * a *
            (y * (d 0 * d 1 * d 2) * y⁻¹ * (d 0 * d 1 * d 2)⁻¹)⁻¹ * a⁻¹) ∈ Q₀ := (hyc a haAt).1
        simpa only [map_mul, map_inv] using h2
      · intro i j hij x hx h
        obtain ⟨a, haO, rfl⟩ := hQR hx
        have haAt : a ∈ At := ⟨hx, haO⟩
        have h' : (d i * d j) * a * (d i * d j)⁻¹ * a⁻¹ ∈ Bt :=
          ⟨by show imgHom Y M _ ∈ Q₀; simpa only [map_mul, map_inv] using h,
            O.mul_mem (hOn.conj_mem a haO _) (O.inv_mem haO)⟩
        have := la_section hD hDc (hdD i) (hdD j) (hdn i j hij) (hdc i j) hAtodd
          (fun x hx => hAtn.conj_mem x hx (d i)) hBtAt haAt h'
        have h2 : imgHom Y M (d i * a * (d i)⁻¹ * a⁻¹) ∈ Q₀ := this.1
        simpa only [map_mul, map_inv] using h2)
  intro i r hr a ha
  have h := hcomm i _ ⟨r, hr, rfl⟩
  have h1 : imgHom Y M (d i * r * (d i)⁻¹ * r⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [h]; group
  exact (hρ1 _).mp h1 a ha

theorem propS_step {D : Set Y} (hD : IsOddTransp D)
    (hDc : ∀ x ∈ D, ∀ g : Y, g * x * g⁻¹ ∈ D) {O : Subgroup Y} [hOn : O.Normal]
    (hOodd : Odd (Nat.card O)) {d : Fin 3 → Y} {t : Y} (hdD : ∀ i, d i ∈ D)
    (hdc : ∀ i j, d i * d j = d j * d i) (hdn : ∀ i j, i ≠ j → d i ≠ d j)
    (ht : ∀ i, t * d i * t⁻¹ = d (i + 1))
    (hcO : ∀ g : Y, (d 0 * d 1 * d 2)⁻¹ * (g * (d 0 * d 1 * d 2) * g⁻¹) ∈ O)
    (hgen : normalClosure ({d 0} : Set Y) = ⊤)
    {A B : Subgroup Y} [hA : A.Normal] [hB : B.Normal] (hBA : B < A) (hAO : A ≤ O)
    (hmin : ∀ N : Subgroup Y, N.Normal → B ≤ N → N ≤ A → N = B ∨ N = A)
    (hIH : ∀ A' B' : Subgroup Y, A'.Normal → B'.Normal → B' < A' → A' ≤ O →
      (∀ N : Subgroup Y, N.Normal → B' ≤ N → N ≤ A' → N = B' ∨ N = A') →
      secSet O A B ⊂ secSet O A' B' →
      ∀ i, ∀ r ∈ O, ∀ a ∈ A',
        (d i * r * (d i)⁻¹ * r⁻¹) * a * (d i * r * (d i)⁻¹ * r⁻¹)⁻¹ * a⁻¹ ∈ B') :
    ∀ i, ∀ r ∈ O, ∀ a ∈ A,
      (d i * r * (d i)⁻¹ * r⁻¹) * a * (d i * r * (d i)⁻¹ * r⁻¹)⁻¹ * a⁻¹ ∈ B := by
  have hAodd : Odd (Nat.card A) := Odd.of_dvd_nat hOodd (card_dvd_of_le hAO)
  have hab := comm_of_chief_odd hBA hAodd hmin
  letI iC : CommGroup (A ⧸ B.subgroupOf A) := secCommGroup A B hab
  letI iA : AddCommGroup (Additive (A ⧸ B.subgroupOf A)) := Additive.addCommGroup
  letI iM : @DistribMulAction Y (Additive (A ⧸ B.subgroupOf A)) _
      (@AddCommMonoid.toAddMonoid _ (@AddCommGroup.toAddCommMonoid _ iA)) :=
    { smul := (secAct A B).smul
      one_smul := (secAct A B).one_smul
      mul_smul := (secAct A B).mul_smul
      smul_zero := (secAct A B).smul_zero
      smul_add := (secAct A B).smul_add }
  have hsurj : ∀ m : Additive (A ⧸ B.subgroupOf A), ∃ a : A,
      Additive.ofMul (QuotientGroup.mk a : A ⧸ B.subgroupOf A) = m := fun m => by
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective m.toMul
    exact ⟨a, by rw [ha]; rfl⟩
  have hfix : ∀ (y : Y) (a : A), y • Additive.ofMul (QuotientGroup.mk a : A ⧸ B.subgroupOf A) =
      Additive.ofMul (QuotientGroup.mk a) ↔ y * a * y⁻¹ * (a : Y)⁻¹ ∈ B :=
    fun y a => secAct_mk_eq_iff A B y a
  refine propS_module hD hDc hOodd hdD hdc hdn ht hcO hgen (A := A) (B := B)
    (M := Additive (A ⧸ B.subgroupOf A)) ?_ ?_ ?_ ?_ hIH
  · rw [show Nat.card (Additive (A ⧸ B.subgroupOf A)) = Nat.card (A ⧸ B.subgroupOf A) from
      Nat.card_congr Additive.toMul]
    exact Odd.of_dvd_nat hAodd (card_quotient_dvd_card _)
  · intro y
    constructor
    · intro h a ha
      exact (hfix y ⟨a, ha⟩).mp (h _)
    · intro h m
      obtain ⟨⟨a, ha⟩, rfl⟩ := hsurj m
      exact (hfix y ⟨a, ha⟩).mpr (h a ha)
  · intro N hN
    let K : Subgroup Y :=
      { carrier := {a | ∃ h : a ∈ A,
          Additive.ofMul (QuotientGroup.mk ⟨a, h⟩ : A ⧸ B.subgroupOf A) ∈ N}
        mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, N.add_mem ha.2 hb.2⟩
        one_mem' := ⟨A.one_mem, N.zero_mem⟩
        inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, N.neg_mem ha.2⟩ }
    have hKn : K.Normal := ⟨fun a ha g => ⟨hA.conj_mem a ha.1 g, hN g _ ha.2⟩⟩
    have hBK : B ≤ K := fun b hb => ⟨hBA.le hb, by
      have : (QuotientGroup.mk ⟨b, hBA.le hb⟩ : A ⧸ B.subgroupOf A) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hb
      rw [this]; exact N.zero_mem⟩
    rcases hmin K hKn hBK (fun a ha => ha.1) with h | h
    · left
      rw [eq_bot_iff]
      intro m hm
      obtain ⟨⟨a, ha⟩, rfl⟩ := hsurj m
      have : a ∈ K := ⟨ha, hm⟩
      rw [h] at this
      rw [AddSubgroup.mem_bot]
      exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff _).mpr this)
    · right
      rw [eq_top_iff]
      intro m _
      obtain ⟨⟨a, ha⟩, rfl⟩ := hsurj m
      have : a ∈ K := by rw [h]; exact ha
      exact this.2
  · intro i j hij m hm
    obtain ⟨⟨a, ha⟩, rfl⟩ := hsurj m
    have h1 := (hfix _ ⟨a, ha⟩).mp hm
    exact (hfix _ ⟨a, ha⟩).mpr (la_section hD hDc (hdD i) (hdD j)
      (hdn i j hij) (hdc i j) hAodd (fun x hx => hA.conj_mem x hx (d i)) hBA.le ha h1)

theorem propS_aux {D : Set Y} (hD : IsOddTransp D)
    (hDc : ∀ x ∈ D, ∀ g : Y, g * x * g⁻¹ ∈ D) {O : Subgroup Y} [hOn : O.Normal]
    (hOodd : Odd (Nat.card O)) {d : Fin 3 → Y} {t : Y} (hdD : ∀ i, d i ∈ D)
    (hdc : ∀ i j, d i * d j = d j * d i) (hdn : ∀ i j, i ≠ j → d i ≠ d j)
    (ht : ∀ i, t * d i * t⁻¹ = d (i + 1))
    (hcO : ∀ g : Y, (d 0 * d 1 * d 2)⁻¹ * (g * (d 0 * d 1 * d 2) * g⁻¹) ∈ O)
    (hgen : normalClosure ({d 0} : Set Y) = ⊤) :
    ∀ A B : Subgroup Y, A.Normal → B.Normal → B < A → A ≤ O →
      (∀ N : Subgroup Y, N.Normal → B ≤ N → N ≤ A → N = B ∨ N = A) →
      ∀ i, ∀ r ∈ O, ∀ a ∈ A,
        (d i * r * (d i)⁻¹ * r⁻¹) * a * (d i * r * (d i)⁻¹ * r⁻¹)⁻¹ * a⁻¹ ∈ B := by
  suffices h : ∀ n : ℕ, ∀ A B : Subgroup Y, (O : Set Y).ncard - (secSet O A B).ncard = n →
      A.Normal → B.Normal → B < A → A ≤ O →
      (∀ N : Subgroup Y, N.Normal → B ≤ N → N ≤ A → N = B ∨ N = A) →
      ∀ i, ∀ r ∈ O, ∀ a ∈ A,
        (d i * r * (d i)⁻¹ * r⁻¹) * a * (d i * r * (d i)⁻¹ * r⁻¹)⁻¹ * a⁻¹ ∈ B by
    intro A B; exact h _ A B rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A B hn hA hB hBA hAO hmin
    haveI := hA
    haveI := hB
    refine propS_step hD hDc hOodd hdD hdc hdn ht hcO hgen hBA hAO hmin ?_
    intro A' B' hA' hB' hBA' hAO' hmin' hss
    refine ih _ ?_ A' B' rfl hA' hB' hBA' hAO' hmin'
    rw [← hn]
    have h1 : (secSet O A B).ncard < (secSet O A' B').ncard :=
      Set.ncard_lt_ncard hss (Set.toFinite _)
    have h2 : (secSet O A' B').ncard ≤ (O : Set Y).ncard :=
      Set.ncard_le_ncard (fun r hr => hr.1) (Set.toFinite _)
    omega

theorem propositionS {s d₁ d₂ d₃ t : Y}
    (hD : IsOddTransp {x : Y | IsConj s x}) (hs : normalClosure ({s} : Set Y) = ⊤)
    (_hL : IsL2OrSz (Y ⧸ fusionZStar Y) 2) (hF : OddCentral.IsFrame s d₁ d₂ d₃ t)
    {A B : Subgroup Y} (hA : A.Normal) (hB : B.Normal) (hBA : B < A) (hAR : A ≤ fusionOddCore Y)
    (hmin : ∀ N : Subgroup Y, N.Normal → B ≤ N → N ≤ A → N = B ∨ N = A)
    (_hmove : ∃ a ∈ A, d₁ * a * d₁⁻¹ * a⁻¹ ∉ B) :
    ∀ d ∈ ({d₁, d₂, d₃} : Set Y), ∀ r ∈ fusionOddCore Y, ∀ a ∈ A,
      (d * r * d⁻¹ * r⁻¹) * a * (d * r * d⁻¹ * r⁻¹)⁻¹ * a⁻¹ ∈ B := by
  obtain ⟨h1, h2, h3, c12, c23, c13, hcZ, h12Z, t1, t2, t3⟩ := hF
  have hDc : ∀ x ∈ {x : Y | IsConj s x}, ∀ g : Y, g * x * g⁻¹ ∈ {x : Y | IsConj s x} :=
    fun x hx g => hx.trans (isConj_iff.mpr ⟨g, rfl⟩)
  have hsq : ∀ x ∈ {x : Y | IsConj s x}, x * x = 1 := fun x hx => by
    have := pow_orderOf_eq_one x; rw [hD.1 _ hx, pow_two] at this; exact this
  have h23Z : d₂ * d₃ ∉ fusionZStar Y := fun h => h12Z (by
    have := (fusionZStar_normal Y).conj_mem _ h t⁻¹
    rwa [show t⁻¹ * (d₂ * d₃) * t⁻¹⁻¹ = d₁ * d₂ by
      calc t⁻¹ * (d₂ * d₃) * t⁻¹⁻¹ = t⁻¹ * ((t * d₁ * t⁻¹) * (t * d₂ * t⁻¹)) * t⁻¹⁻¹ := by
            rw [t1, t2]
        _ = d₁ * d₂ := by group] at this)
  have h31Z : d₃ * d₁ ∉ fusionZStar Y := fun h => h23Z (by
    have := (fusionZStar_normal Y).conj_mem _ h t⁻¹
    rwa [show t⁻¹ * (d₃ * d₁) * t⁻¹⁻¹ = d₂ * d₃ by
      calc t⁻¹ * (d₃ * d₁) * t⁻¹⁻¹ = t⁻¹ * ((t * d₂ * t⁻¹) * (t * d₃ * t⁻¹)) * t⁻¹⁻¹ := by
            rw [t2, t3]
        _ = d₂ * d₃ := by group] at this)
  have hne : ∀ x y : Y, x ∈ {x : Y | IsConj s x} → x * y ∉ fusionZStar Y → x ≠ y :=
    fun x y hx hxy h => hxy (by rw [← h, hsq x hx]; exact one_mem _)
  have n12 := hne _ _ h1 h12Z
  have n23 := hne _ _ h2 h23Z
  have n31 := hne _ _ h3 h31Z
  let d : Fin 3 → Y := ![d₁, d₂, d₃]
  have hdD : ∀ i, d i ∈ {x : Y | IsConj s x} := by
    intro i; fin_cases i
    · exact h1
    · exact h2
    · exact h3
  have hdc : ∀ i j, d i * d j = d j * d i := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact c12.eq
    · exact c13.eq
    · exact c12.symm.eq
    · rfl
    · exact c23.eq
    · exact c13.symm.eq
    · exact c23.symm.eq
    · rfl
  have hdn : ∀ i j, i ≠ j → d i ≠ d j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact n12
    · exact n31.symm
    · exact n12.symm
    · exact absurd rfl hij
    · exact n23
    · exact n31
    · exact n23.symm
    · exact absurd rfl hij
  have ht : ∀ i, t * d i * t⁻¹ = d (i + 1) := by
    intro i; fin_cases i
    · exact t1
    · exact t2
    · exact t3
  have hcO : ∀ g : Y, (d 0 * d 1 * d 2)⁻¹ * (g * (d 0 * d 1 * d 2) * g⁻¹) ∈ fusionOddCore Y := by
    intro g
    have hc := mem_center_iff.mp (mem_comap.mp hcZ) (QuotientGroup.mk' (fusionOddCore Y) g)
    rw [← QuotientGroup.ker_mk' (fusionOddCore Y), MonoidHom.mem_ker]
    show QuotientGroup.mk' (fusionOddCore Y) ((d₁ * d₂ * d₃)⁻¹ * (g * (d₁ * d₂ * d₃) * g⁻¹)) = 1
    generalize d₁ * d₂ * d₃ = c at hc ⊢
    simp only [map_mul, map_inv]
    rw [hc]
    group
  have hgen : normalClosure ({d 0} : Set Y) = ⊤ := by
    obtain ⟨g, hg⟩ := isConj_iff.mp h1
    rw [eq_top_iff, ← hs]
    refine normalClosure_le_normal (Set.singleton_subset_iff.mpr ?_)
    have := (normalClosure_normal (s := ({d 0} : Set Y))).conj_mem _
      (subset_normalClosure (Set.mem_singleton _)) g⁻¹
    rwa [show g⁻¹ * d 0 * g⁻¹⁻¹ = s by
      show g⁻¹ * d₁ * g⁻¹⁻¹ = s
      rw [← hg]; group] at this
  have key := propS_aux hD hDc (odd_card_fusionOddCore Y) hdD hdc hdn ht hcO hgen A B hA hB hBA
    hAR hmin
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact key 0
  · exact key 1
  · exact key 2

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

