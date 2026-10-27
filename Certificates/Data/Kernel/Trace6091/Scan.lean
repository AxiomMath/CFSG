module

public import Certificates.Data.Kernel.KDense.Twins

public section

namespace CFSG.KC.KDense

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

@[expose] noncomputable def OCTS : Nat :=
  nat_lit 0xfeffdffcffcefcdfccfcbfcafc9fc7fc6fc5fc3fc0fbefbdfbbfb7faff9ff7ef7df7bf77f6ff5ff3ef37f36f34f32f30f26f24f22f16f14f12f06f00efeefdefbef7eefedfebeebdebbeb7eafe9fe77e5fe57e56e55e54e53e52e51e47e46e45e43e40e3ee2fe2ee2ce2ae28e26e24e22e0ee0ce0ae06e00dfedfddfbdf7defddfdb7dafda7da6da5da4da3da2da1d87d86d85d83d80d7ed7dd7bd77d6fd5fd3ed1fd1ed1cd1ad18d16d14d12d0ed0cd0ad06d00cfdcf7cf5cf4cf1cf0ce5ce4ce1cd5cd4cd1cc5cc0cbdc9fc9dc9cc99c98c95c94c91c8dc8cc89c85c80c7dc6fc6dc6cc69c68c65c64c61c4dc4cc49c45c40c3ec3dc3cc38c34c30c2cc28c24c1cc18c14c0cc00bfebfdbfbbf7befbdfbbebbdbbbbb7bafb9fb77b6fb67b66b65b64b63b62b61b47b46b45b43b40b3eb1fb1eb1cb1ab18b16b14b12b0eb0cb0ab06b00afeafdafbaf7aefadfaafa9fa8fa8ea8da8ca8ba8aa89a87a86a85a83a80a7ea7da7ba77a6fa5fa3ea37a36a34a32a30a26a24a22a16a14a12a06a009f79df9d79d69d59d49d39d29d19c79c69c59c39c09be9bd9bb9b79af99f97e97d97b97796f95f93e92f92e92c92a92892692492290e90c90a9069008fd8ef8ed8ec8e98e88e58e48e18cd8cc8c98c58c08bd8b78b58b48b18b08a58a48a189589489188588087d85f85d85c85985885585485184d84c84984584083e83d83c83883483082c82882481c81881480c8007fe7fd7fb7f77ef7df7b779f79779679579479379279178778678578378077e77d77b77776f75f73e72f72e72c72a72872672472270e70c70a7067006f76ef6e76e66e56e46e36e26e16c76c66c56c36c06be6bd6bb6b76af69f67e67d67b67766f65f63e61f61e61c61a61861661461260e60c60a6066005fe5fd5fb5f75ef5df5be5bd5bb5b75af59f56f55f54f54e54d54c54b54a54954754654554354053e5375365345325305265245225165145125065004fd4df4dd4dc4d94d84d54d44d14cd4cc4c94c54c04bd4af4ad4ac4a94a84a54a44a148d48c48948548047d47747547447147046546446145545445144544043e43d43c43843443042c42842441c41841440c4003fb3f73f33f23f13f03e33e23e13d33d23d13c33c03bb3af3ab3aa3a93a83a33a23a138b38a38938338037b35f35b35a35935835335235134b34a34934334033e33b33a33833233032a32832231a31831230a3002fb2df2db2da2d92d82d32d22d12cb2ca2c92c32c02bb2b72b32b22b12b02a32a22a129329229128328027b26f26b26a26926826326226124b24a24924324023e23b23a23823223022a22822221a21821220a2001fb1ef1eb1ea1e91e81e31e21e11cb1ca1c91c31c01bb19f19b19a19919819319219118b18a18918318017b17717317217117016316216115315215114314013e13b13a13813213012a12812211a11811210a1000fd0fb0f90f80f10f00e90e80e10d90d80d10c90c00bd0bb0b90b80b10b00a90a80a109909809108908007d07b07907807107006906806105905805104904003002802402202102001801401201101000c00a009008006005004003002001

@[expose] noncomputable def octT (o : Nat) : Nat := fld(OCTS, Nat.mul (nat_lit 12) o, nat_lit 4095)

@[expose] noncomputable def EVS : Nat :=
  nat_lit 0xfdf7df8efd3971dfb3569cd971e0bf72d59ad569d09d365c88f121417ef1d396cd59b05cb55a84e911213c74d982e509111e305090c14180

@[expose] noncomputable def evenT (m : Nat) : Nat := fld(EVS, Nat.mul (nat_lit 7) m, nat_lit 127)

@[expose] noncomputable def pW (w : Nat) : Nat :=
  Nat.land (Nat.shiftRight (popcT (nat_lit 24) w) (nat_lit 2)) (nat_lit 1)

@[expose] noncomputable def strictZ (y : Nat) (k : Nat → Int) : Int :=
  Nat.rec (motive := fun _ => Int) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def selZ (b : Bool) (x : Int) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.ofNat 0) x b

@[expose] noncomputable def sgnZ (b : Bool) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.ofNat 1) (Int.negSucc 0) b

@[expose] noncomputable def xTermT (P BT a u : Nat) : Int :=
  selZ (Nat.beq (permCT P a) a)
    (selZ (Nat.beq (permDT P u) u) (sgnZ (Nat.beq (kappaT BT a) (nat_lit 1))))

@[expose] noncomputable def sumZ (n : Nat) (f : Nat → Int) : Int :=
  Nat.rec (motive := fun _ => Int) (Int.ofNat 0) (fun i acc => Int.add acc (f i)) n

@[expose] noncomputable def oddRowT (P BT c w pc : Nat) : Int :=
  sumZ (nat_lit 24) (fun i => strictZ (Nat.xor c (selB (Nat.xor (bitN w i) pc) (nat_lit 63)))
    (fun a => xTermT P BT a (dualT (Nat.shiftLeft (nat_lit 1) i))))

@[expose] noncomputable def oddScanT (P BT t₀ n : Nat) : Int :=
  sumZ n (fun j => strictZ (Nat.mul (nat_lit 2) (Nat.add t₀ j)) (fun c =>
    strictZ (wordT c) (fun w => strictZ (pW w) (fun pc => oddRowT P BT c w pc))))

end CFSG.KC.KDense

end
