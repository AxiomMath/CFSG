module

public import CFSG.Quasithin.Background.HZ82Base
public import CFSG.Quasithin.Background.HModChk

public section

namespace CFSG.Quasithin.H.Coc

open CFSG.Open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.ZTrans

section Deriv

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem deriv_one {H : Subgroup (MulAut V)} {δ : MulAut V → V}
    (hδ : ∀ g ∈ H, ∀ k ∈ H, δ (g * k) = δ g * g (δ k)) : δ 1 = 1 := by
  have h := hδ 1 H.one_mem 1 H.one_mem
  rw [mul_one, MulAut.one_apply] at h
  exact left_eq_mul.1 h

theorem eq_inner_of_closure {H : Subgroup (MulAut V)} {δ : MulAut V → V}
    (hδ : ∀ g ∈ H, ∀ k ∈ H, δ (g * k) = δ g * g (δ k)) {Γ : Set (MulAut V)} (hΓ : Γ ⊆ H)
    {w : V} (hw : ∀ g ∈ Γ, δ g = w * (g w)⁻¹) :
    ∀ g ∈ Subgroup.closure Γ, δ g = w * (g w)⁻¹ := by
  let K : Subgroup (MulAut V) :=
    { carrier := {g | g ∈ H ∧ δ g = w * (g w)⁻¹}
      mul_mem' := fun {g k} hg hk => by
        refine ⟨H.mul_mem hg.1 hk.1, ?_⟩
        rw [hδ g hg.1 k hk.1, hg.2, hk.2, map_mul, map_inv, MulAut.mul_apply, mul_assoc,
          inv_mul_cancel_left]
      one_mem' := ⟨H.one_mem, by rw [deriv_one hδ, MulAut.one_apply, mul_inv_cancel]⟩
      inv_mem' := fun {g} hg => by
        refine ⟨H.inv_mem hg.1, ?_⟩
        have h1 := hδ g hg.1 g⁻¹ (H.inv_mem hg.1)
        rw [mul_inv_cancel, deriv_one hδ, hg.2] at h1
        have h2 : g (δ g⁻¹) = g w * w⁻¹ := by
          rw [eq_inv_of_mul_eq_one_right h1.symm, mul_inv_rev, inv_inv]
        apply g.injective
        rw [h2, map_mul, map_inv, MulAut.apply_inv_self] }
  have hle : Subgroup.closure Γ ≤ K := (Subgroup.closure_le K).2 fun g hg => ⟨hΓ hg, hw g hg⟩
  exact fun g hg => (hle hg).2

theorem coc_of_map [Finite V] [Finite W] (e : V ≃* W) {H : Subgroup (MulAut V)} {z : V}
    {δ : MulAut V → V} (hδ : ∀ g ∈ H, ∀ k ∈ H, δ (g * k) = δ g * g (δ k))
    (hR : ∀ r ∈ radZ H z, δ r ∈ Subgroup.zpowers z)
    (hstd : ∀ δ₀ : MulAut W → W, (∀ g ∈ H.map (congrHom e), ∀ k ∈ H.map (congrHom e),
        δ₀ (g * k) = δ₀ g * g (δ₀ k)) →
      (∀ r ∈ radZ (H.map (congrHom e)) (e z), δ₀ r ∈ Subgroup.zpowers (e z)) →
      ∃ w ∈ vZ (H.map (congrHom e)) (e z), ∀ g ∈ H.map (congrHom e), δ₀ g = w * (g w)⁻¹) :
    ∃ w ∈ vZ H z, ∀ g ∈ H, δ g = w * (g w)⁻¹ := by
  have hback : ∀ g : MulAut V, congrHom e.symm (congrHom e g) = g := fun g => by
    ext v
    simp
  have happ : ∀ (g : MulAut V) (v : V), congrHom e g (e v) = e (g v) := fun g v => by
    rw [congrHom_apply, MulEquiv.symm_apply_apply]
  have hz : Subgroup.zpowers (e z) = (Subgroup.zpowers z).map e.toMonoidHom :=
    (MonoidHom.map_zpowers e.toMonoidHom z).symm
  obtain ⟨w₀, hw₀, hδ₀⟩ := hstd (fun g => e (δ (congrHom e.symm g)))
    (by
      rintro _ ⟨g, hg, rfl⟩ _ ⟨k, hk, rfl⟩
      rw [← map_mul (congrHom e) g k, hback, hback, hback, hδ g hg k hk, map_mul, happ])
    (by
      intro r hr
      rw [← radZ_map] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      show e (δ (congrHom e.symm (congrHom e r'))) ∈ _
      rw [hback, hz]
      exact ⟨δ r', hR r' hr', rfl⟩)
  rw [← vZ_map] at hw₀
  obtain ⟨w, hw, rfl⟩ := hw₀
  refine ⟨w, hw, fun g hg => ?_⟩
  have h : e (δ (congrHom e.symm (congrHom e g))) = e w * (congrHom e g (e w))⁻¹ :=
    hδ₀ (congrHom e g) ⟨g, hg, rfl⟩
  rw [hback, happ, ← map_inv, ← map_mul] at h
  exact e.injective h

end Deriv

variable {n : ℕ}

theorem toW_inv_self (n m : ℕ) : (toW n m)⁻¹ = toW n m := by
  refine inv_eq_of_mul_eq_one_right ?_
  have h := toW_xor n m m
  rw [Nat.xor_self, toW_zero] at h
  exact h.symm

theorem eq_of_xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b :=
  calc a = a ^^^ b ^^^ b := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    _ = b := by rw [h, Nat.zero_xor]

@[expose] def ActsBy (g : MulAut (Wn n)) (c : List ℕ) : Prop :=
  ∀ m, g (toW n m) = toW n (actM c m)

theorem actsBy_of_lt {g : MulAut (Wn n)} {c : List ℕ} (hc : c.length = n)
    (h : ∀ m < 2 ^ n, g (toW n m) = toW n (actM c m)) : ActsBy g c := fun m => by
  have h1 : g (toW n m) = g (toW n (m % 2 ^ n)) := by rw [toW_mod]
  rw [h1, h _ (Nat.mod_lt _ (Nat.two_pow_pos n))]
  exact congrArg (toW n) (by rw [← hc]; exact actM_mod c m)

theorem actsBy_of_xorLin {g : MulAut (Wn n)} {f : ℕ → ℕ} (hf : XorLin f)
    (h : ∀ m, g (toW n m) = toW n (f m)) : ActsBy g (matOf n f) :=
  actsBy_of_lt (length_matOf n f) fun m hm => by rw [h, actM_matOf hf n m hm]

@[expose] def wProd {G : Type*} [Group G] (gs : List G) : List ℕ → G
  | [] => 1
  | i :: u => gs.getD i 1 * wProd gs u

@[expose] def wAct (cs : List (List ℕ)) : List ℕ → ℕ → ℕ
  | [], m => m
  | i :: u, m => actM (cs.getD i []) (wAct cs u m)

@[expose] def fox (cs : List (List ℕ)) (d : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | i :: u => d i ^^^ actM (cs.getD i []) (fox cs d u)

theorem wProd_mem {G : Type*} [Group G] {K : Subgroup G} {gs : List G}
    (h : ∀ i < gs.length, gs.getD i 1 ∈ K) : ∀ u, wProd gs u ∈ K
  | [] => K.one_mem
  | i :: u => by
    refine K.mul_mem ?_ (wProd_mem h u)
    by_cases hi : i < gs.length
    · exact h i hi
    · rw [List.getD_eq_default _ _ (by omega)]
      exact K.one_mem

theorem wProd_toW {gs : List (MulAut (Wn n))} {cs : List (List ℕ)}
    (h : ∀ i < gs.length, ActsBy (gs.getD i 1) (cs.getD i [])) :
    ∀ u : List ℕ, (∀ i ∈ u, i < gs.length) → ∀ m, wProd gs u (toW n m) = toW n (wAct cs u m)
  | [], _, m => rfl
  | i :: u, hu, m => by
    show (gs.getD i 1 * wProd gs u) (toW n m) = toW n (actM (cs.getD i []) (wAct cs u m))
    rw [MulAut.mul_apply, wProd_toW h u (fun j hj => hu j (List.mem_cons_of_mem i hj)) m]
    exact h i (hu i List.mem_cons_self) _

theorem xorLin_wAct (cs : List (List ℕ)) : ∀ u : List ℕ, XorLin (wAct cs u)
  | [] => fun _ _ => rfl
  | i :: u => fun a b => by
    show actM _ (wAct cs u (a ^^^ b)) = actM _ (wAct cs u a) ^^^ actM _ (wAct cs u b)
    rw [xorLin_wAct cs u, actM_xor]

theorem wProd_eq_one {gs : List (MulAut (Wn n))} {cs : List (List ℕ)}
    (h : ∀ i < gs.length, ActsBy (gs.getD i 1) (cs.getD i [])) {u : List ℕ}
    (hu : ∀ i ∈ u, i < gs.length) (hid : matOf n (wAct cs u) = matOf n id) :
    wProd gs u = 1 := by
  ext w
  obtain ⟨m, hm, rfl⟩ := toW_surj n w
  rw [wProd_toW h u hu, MulAut.one_apply, ← actM_matOf (xorLin_wAct cs u) n m hm, hid,
    actM_matOf (f := id) (fun _ _ => rfl) n m hm]
  rfl

theorem wProd_eq {gs : List (MulAut (Wn n))} {cs : List (List ℕ)}
    (h : ∀ i < gs.length, ActsBy (gs.getD i 1) (cs.getD i [])) {u : List ℕ}
    (hu : ∀ i ∈ u, i < gs.length) {ρ : MulAut (Wn n)} {c : List ℕ} (hρ : ActsBy ρ c)
    (hc : matOf n (wAct cs u) = c) : wProd gs u = ρ := by
  ext w
  obtain ⟨m, hm, rfl⟩ := toW_surj n w
  rw [wProd_toW h u hu, hρ m, ← actM_matOf (xorLin_wAct cs u) n m hm, hc]

theorem fox_lt {cs : List (List ℕ)} {d : ℕ → ℕ} {k : ℕ}
    (hcs : ∀ i < k, ∀ c ∈ cs.getD i [], c < 2 ^ n) (hd : ∀ i < k, d i < 2 ^ n) :
    ∀ u : List ℕ, (∀ i ∈ u, i < k) → fox cs d u < 2 ^ n
  | [], _ => Nat.two_pow_pos n
  | i :: _, hu => Nat.xor_lt_two_pow (hd i (hu i List.mem_cons_self))
    (actM_lt (hcs i (hu i List.mem_cons_self)) _)

theorem fox_spec {H₀ : Subgroup (MulAut (Wn n))} {δ : MulAut (Wn n) → Wn n}
    (hδ : ∀ g ∈ H₀, ∀ k ∈ H₀, δ (g * k) = δ g * g (δ k)) {gs : List (MulAut (Wn n))}
    {cs : List (List ℕ)} {d : ℕ → ℕ} (hmem : ∀ i < gs.length, gs.getD i 1 ∈ H₀)
    (hact : ∀ i < gs.length, ActsBy (gs.getD i 1) (cs.getD i []))
    (hval : ∀ i < gs.length, δ (gs.getD i 1) = toW n (d i)) :
    ∀ u : List ℕ, (∀ i ∈ u, i < gs.length) → δ (wProd gs u) = toW n (fox cs d u)
  | [], _ => (deriv_one hδ).trans (toW_zero n).symm
  | i :: u, hu => by
    have hi := hu i List.mem_cons_self
    have hu' : ∀ j ∈ u, j < gs.length := fun j hj => hu j (List.mem_cons_of_mem i hj)
    show δ (gs.getD i 1 * wProd gs u) = toW n (d i ^^^ actM (cs.getD i []) (fox cs d u))
    rw [hδ _ (hmem i hi) _ (wProd_mem hmem u), hval i hi, fox_spec hδ hmem hact hval u hu',
      hact i hi (fox cs d u), toW_xor]

theorem xorLin_fox (cs : List (List ℕ)) (d d' : ℕ → ℕ) :
    ∀ u : List ℕ, fox cs (fun i => d i ^^^ d' i) u = fox cs d u ^^^ fox cs d' u
  | [] => (Nat.zero_xor 0).symm
  | i :: u => by
    show (d i ^^^ d' i) ^^^ actM _ (fox cs (fun i => d i ^^^ d' i) u) =
      (d i ^^^ actM _ (fox cs d u)) ^^^ (d' i ^^^ actM _ (fox cs d' u))
    rw [xorLin_fox cs d d' u, actM_xor]
    ac_rfl

theorem xorLin_add_self {f : ℕ → ℕ} (hf : XorLin f) : XorLin fun v => v ^^^ f v :=
  fun a b => by
    show a ^^^ b ^^^ f (a ^^^ b) = a ^^^ f a ^^^ (b ^^^ f b)
    rw [hf]
    ac_rfl

@[expose] def projZ (p z v : ℕ) : ℕ := v ^^^ actM [z] (v >>> p)

theorem xorLin_projZ (p z : ℕ) : XorLin (projZ p z) :=
  xorLin_add_self (f := fun v => actM [z] (v >>> p)) fun a b => by
    show actM [z] ((a ^^^ b) >>> p) = actM [z] (a >>> p) ^^^ actM [z] (b >>> p)
    rw [Nat.shiftRight_xor_distrib, actM_xor]

theorem projZ_zero (p z : ℕ) : projZ p z 0 = 0 := (xorLin_projZ p z).map_zero

@[expose] def dOf (n v i : ℕ) : ℕ := if i = 0 then v % 2 ^ n else v >>> n

theorem xorLin_dOf (n i : ℕ) : XorLin fun v => dOf n v i := fun a b => by
  show (if i = 0 then (a ^^^ b) % 2 ^ n else (a ^^^ b) >>> n) =
    (if i = 0 then a % 2 ^ n else a >>> n) ^^^ (if i = 0 then b % 2 ^ n else b >>> n)
  split_ifs
  · exact Nat.xor_mod_two_pow
  · exact Nat.shiftRight_xor_distrib

@[expose] def conVal (cs : List (List ℕ)) (n p z : ℕ) : Option ℕ → List ℕ → ℕ → ℕ
  | none, u, v => fox cs (dOf n v) u
  | some _, u, v => projZ p z (fox cs (dOf n v) u)

@[expose] def conSum (cs : List (List ℕ)) (n p z : ℕ) :
    List (Option ℕ × List ℕ × List ℕ) → ℕ → ℕ
  | [], _ => 0
  | c :: cons, v => actM c.2.2 (conVal cs n p z c.1 c.2.1 v) ^^^ conSum cs n p z cons v

@[expose] def consOK (n K : ℕ) (cs : List (List ℕ)) (tcols : ℕ → List ℕ)
    (cons : List (Option ℕ × List ℕ × List ℕ)) : Bool :=
  cons.all fun c => c.2.1.all (· < 2) && c.1.all (· < K) &&
    matOf n (wAct cs c.2.1) == c.1.elim (matOf n id) tcols

theorem xorLin_conVal (cs : List (List ℕ)) (n p z : ℕ) (r : Option ℕ) (u : List ℕ) :
    XorLin (conVal cs n p z r u) := fun a b => by
  have h : fox cs (dOf n (a ^^^ b)) u = fox cs (dOf n a) u ^^^ fox cs (dOf n b) u := by
    rw [← xorLin_fox]
    exact congrArg (fun d => fox cs d u) (funext fun i => xorLin_dOf n i a b)
  cases r
  · exact h
  · show projZ p z (fox cs (dOf n (a ^^^ b)) u) =
      projZ p z (fox cs (dOf n a) u) ^^^ projZ p z (fox cs (dOf n b) u)
    rw [h, xorLin_projZ]

theorem xorLin_conSum (cs : List (List ℕ)) (n p z : ℕ) :
    ∀ cons : List (Option ℕ × List ℕ × List ℕ), XorLin (conSum cs n p z cons)
  | [] => fun _ _ => (Nat.zero_xor 0).symm
  | c :: cons => fun a b => by
    show actM c.2.2 (conVal cs n p z c.1 c.2.1 (a ^^^ b)) ^^^ conSum cs n p z cons (a ^^^ b) =
      (actM c.2.2 (conVal cs n p z c.1 c.2.1 a) ^^^ conSum cs n p z cons a) ^^^
        (actM c.2.2 (conVal cs n p z c.1 c.2.1 b) ^^^ conSum cs n p z cons b)
    rw [xorLin_conVal, actM_xor, xorLin_conSum cs n p z cons]
    ac_rfl

theorem conSum_eq_zero (cs : List (List ℕ)) (n p z v : ℕ) :
    ∀ cons : List (Option ℕ × List ℕ × List ℕ), (∀ c ∈ cons, conVal cs n p z c.1 c.2.1 v = 0) →
      conSum cs n p z cons v = 0
  | [], _ => rfl
  | c :: cons, h => by
    show actM c.2.2 (conVal cs n p z c.1 c.2.1 v) ^^^ conSum cs n p z cons v = 0
    rw [h c List.mem_cons_self, (actM_xor _).map_zero,
      conSum_eq_zero cs n p z v cons fun c' hc' => h c' (List.mem_cons_of_mem c hc'),
      Nat.xor_zero]

theorem eq_of_cert {G : ℕ → ℕ} (hG : XorLin G) {Bc Φc : List ℕ} {N : ℕ}
    (h : matOf N (fun v => v ^^^ actM Bc (actM Φc v)) = matOf N G) {v : ℕ} (hv : v < 2 ^ N)
    (h0 : G v = 0) : v = actM Bc (actM Φc v) := by
  have hf : XorLin fun v => v ^^^ actM Bc (actM Φc v) :=
    xorLin_add_self ((actM_xor Bc).comp (actM_xor Φc))
  have h1 := actM_matOf hf N v hv
  rw [h, actM_matOf hG N v hv, h0] at h1
  exact eq_of_xor_eq_zero h1.symm

@[expose] def packB (n : ℕ) (c₀ c₁ : List ℕ) (w : ℕ) : ℕ :=
  (actM c₀ w ^^^ w) ^^^ ((actM c₁ w ^^^ w) <<< n)

theorem xorLin_packB (n : ℕ) (c₀ c₁ : List ℕ) : XorLin (packB n c₀ c₁) := fun a b => by
  unfold packB
  rw [actM_xor, actM_xor, show actM c₁ a ^^^ actM c₁ b ^^^ (a ^^^ b) =
    (actM c₁ a ^^^ a) ^^^ (actM c₁ b ^^^ b) by ac_rfl, Nat.shiftLeft_xor_distrib]
  ac_rfl

theorem pack_mod {x y : ℕ} (hx : x < 2 ^ n) : (x ^^^ (y <<< n)) % 2 ^ n = x := by
  rw [Nat.xor_mod_two_pow, Nat.shiftLeft_eq, Nat.mul_mod_left, Nat.xor_zero, Nat.mod_eq_of_lt hx]

theorem pack_shift {x y : ℕ} (hx : x < 2 ^ n) : (x ^^^ (y <<< n)) >>> n = y := by
  rw [Nat.shiftRight_xor_distrib, Nat.shiftLeft_shiftRight, Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt hx, Nat.zero_xor]

theorem pack_lt {x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n) : x ^^^ (y <<< n) < 2 ^ (2 * n) := by
  refine Nat.xor_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))) ?_
  rw [Nat.shiftLeft_eq, two_mul, pow_add]
  exact Nat.mul_lt_mul_of_pos_right hy (Nat.two_pow_pos n)

theorem mem_combos_of_mem : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ∈ combos l
  | [], _, h => by simp at h
  | b :: l, a, h => by
    rw [combos, List.mem_append, List.mem_map]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inr ⟨0, zero_mem_combos l, Nat.zero_xor _⟩
    · exact Or.inl (mem_combos_of_mem h)

theorem eq_one_or_of_mem_zpowers {G : Type*} [Group G] {x y : G} (hy : y * y = 1)
    (h : x ∈ Subgroup.zpowers y) : x = 1 ∨ x = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  have h2 : y ^ (2 : ℤ) = 1 := by rw [zpow_two, hy]
  rw [← Int.mul_ediv_add_emod k 2, zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exact Or.inl (by rw [h0, zpow_zero])
  · exact Or.inr (by rw [h1, zpow_one])

theorem eq_inner_std {H₀ R : Subgroup (MulAut (Wn n))} {δ : MulAut (Wn n) → Wn n}
    (hδ : ∀ g ∈ H₀, ∀ k ∈ H₀, δ (g * k) = δ g * g (δ k)) {p z : ℕ}
    (hR : ∀ r ∈ R, δ r ∈ Subgroup.zpowers (toW n z)) (hz : z < 2 ^ n) (hpz : projZ p z z = 0)
    {g₀ g₁ : MulAut (Wn n)} (hH : H₀ ≤ Subgroup.closure {g₀, g₁}) (hg₀ : g₀ ∈ H₀)
    (hg₁ : g₁ ∈ H₀) {c₀ c₁ : List ℕ} (ha₀ : ActsBy g₀ c₀) (ha₁ : ActsBy g₁ c₁)
    (hlt : ∀ c ∈ c₀ ++ c₁, c < 2 ^ n) {K : ℕ} {tcols : ℕ → List ℕ}
    (htgt : ∀ t < K, ∃ ρ ∈ R, ActsBy ρ (tcols t)) {cons : List (Option ℕ × List ℕ × List ℕ)}
    (hok : consOK n K [c₀, c₁] tcols cons = true) {w0 Φc : List ℕ} (hw0 : ∀ w ∈ w0, w < 2 ^ n)
    (hcert : matOf (2 * n) (fun v => v ^^^ actM (w0.map (packB n c₀ c₁)) (actM Φc v)) =
      matOf (2 * n) (conSum [c₀, c₁] n p z cons)) :
    ∃ m ∈ combos w0, ∀ g ∈ H₀, δ g = toW n m * (g (toW n m))⁻¹ := by
  obtain ⟨a, ha, hae⟩ := toW_surj n (δ g₀)
  obtain ⟨b, hb, hbe⟩ := toW_surj n (δ g₁)
  have hd0 : dOf n (a ^^^ (b <<< n)) 0 = a := by
    rw [dOf, ite_eq_left rfl, pack_mod ha]
  have hd1 : dOf n (a ^^^ (b <<< n)) 1 = b := by
    rw [dOf, ite_eq_right one_ne_zero, pack_shift ha]
  have hlt0 : ∀ c ∈ c₀, c < 2 ^ n := fun c hc => hlt c (List.mem_append_left _ hc)
  have hlt1 : ∀ c ∈ c₁, c < 2 ^ n := fun c hc => hlt c (List.mem_append_right _ hc)
  have hmem : ∀ i < [g₀, g₁].length, [g₀, g₁].getD i 1 ∈ H₀ := by
    intro i hi
    rcases i with _ | _ | i
    · exact hg₀
    · exact hg₁
    · simp at hi
  have hact : ∀ i < [g₀, g₁].length, ActsBy ([g₀, g₁].getD i 1) ([c₀, c₁].getD i []) := by
    intro i hi
    rcases i with _ | _ | i
    · exact ha₀
    · exact ha₁
    · simp at hi
  have hval : ∀ i < [g₀, g₁].length,
      δ ([g₀, g₁].getD i 1) = toW n (dOf n (a ^^^ (b <<< n)) i) := by
    intro i hi
    rcases i with _ | _ | i
    · rw [hd0]
      exact hae.symm
    · rw [hd1]
      exact hbe.symm
    · simp at hi
  have hcsl : ∀ i < 2, ∀ c ∈ [c₀, c₁].getD i [], c < 2 ^ n := by
    intro i hi
    rcases i with _ | _ | i
    · exact hlt0
    · exact hlt1
    · omega
  have hdl : ∀ i < 2, dOf n (a ^^^ (b <<< n)) i < 2 ^ n := by
    intro i hi
    rcases i with _ | _ | i
    · rw [hd0]
      exact ha
    · rw [hd1]
      exact hb
    · omega
  have hcon : ∀ c ∈ cons, conVal [c₀, c₁] n p z c.1 c.2.1 (a ^^^ (b <<< n)) = 0 := by
    intro c hc
    have h := List.all_eq_true.1 hok c hc
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨hu, hK⟩, hw⟩ := h
    have hfox := fox_spec hδ hmem hact hval c.2.1 hu
    have hflt := fox_lt hcsl hdl c.2.1 hu
    rcases hr : c.1 with _ | t
    · rw [hr] at hw
      rw [wProd_eq_one hact hu hw] at hfox
      exact toW_inj hflt (Nat.two_pow_pos n)
        (hfox.symm.trans ((deriv_one hδ).trans (toW_zero n).symm))
    · rw [hr] at hw hK
      obtain ⟨ρ, hρR, hρ⟩ := htgt t (by simpa using hK)
      rw [wProd_eq hact hu hρ hw] at hfox
      have hy : toW n z * toW n z = 1 := by
        have h2 := toW_xor n z z
        rw [Nat.xor_self, toW_zero] at h2
        exact h2.symm
      show projZ p z (fox [c₀, c₁] (dOf n (a ^^^ (b <<< n))) c.2.1) = 0
      rcases eq_one_or_of_mem_zpowers hy (hR ρ hρR) with h3 | h3
      · rw [hfox, ← toW_zero n] at h3
        rw [toW_inj hflt (Nat.two_pow_pos n) h3, projZ_zero]
      · rw [hfox] at h3
        rw [toW_inj hflt hz h3, hpz]
  have hv := eq_of_cert (xorLin_conSum [c₀, c₁] n p z cons) hcert (pack_lt ha hb)
    (conSum_eq_zero [c₀, c₁] n p z _ cons hcon)
  rw [actM_map (xorLin_packB n c₀ c₁)] at hv
  set m := actM w0 (actM Φc (a ^^^ (b <<< n)))
  have hm : m ∈ combos w0 := actM_mem_combos (fun w hw => mem_combos_of_mem hw) _
  have hml : m < 2 ^ n := combos_lt hw0 m hm
  have hA : a = actM c₀ m ^^^ m := by
    have h := congrArg (· % 2 ^ n) hv
    rwa [pack_mod ha, packB, pack_mod (Nat.xor_lt_two_pow (actM_lt hlt0 _) hml)] at h
  have hB : b = actM c₁ m ^^^ m := by
    have h := congrArg (· >>> n) hv
    rwa [pack_shift ha, packB, pack_shift (Nat.xor_lt_two_pow (actM_lt hlt0 _) hml)] at h
  have hinner : ∀ (g : MulAut (Wn n)) (c : List ℕ), ActsBy g c →
      toW n (actM c m ^^^ m) = toW n m * (g (toW n m))⁻¹ := fun g c hg => by
    rw [hg m, toW_inv_self, ← toW_xor, Nat.xor_comm]
  refine ⟨m, hm, fun g hg => eq_inner_of_closure hδ ?_ ?_ g (hH hg)⟩
  · rintro _ (rfl | rfl)
    · exact hg₀
    · exact hg₁
  · rintro _ (rfl | rfl)
    · rw [← hae, hA]
      exact hinner _ _ ha₀
    · rw [← hbe, hB]
      exact hinner _ _ ha₁

end CFSG.Quasithin.H.Coc
